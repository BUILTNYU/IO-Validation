from collections import defaultdict
from collections import OrderedDict
from datetime import datetime
from datetime import timedelta
import os
import sys
import math
import pandas as pd
import operator
import random

speedlimit = {
'motorway':120,
'trunk':100,
'primary':80,
'secondary':60,
'tertiary':60,
'residential':40,
'unclassified':40,
'motorway_link':50,
'trunk_link':50,
'primary_link':50,
'secondary_link':30,
'tertiary_link':30,
'service':20,
'living_street':20,
}

class Cgraph:
    
    def __init__(self, layerName):
        self.layers = iface.mapCanvas().layers()
        self.layer = [layer for layer in self.layers if layer.name() == layerName][0]
        self.features = self.layer.getFeatures()
        self.distance = QgsDistanceArea()
        self.distance.setEllipsoid('WGS84')
        self.allActiveEdges = set();
        self.startNode = 0;
        self.endNode = 0;

        self.grid_size = 0
        self.XBase = 0
        self.link_grid = defaultdict(list)
        
        self.intersections = defaultdict(list) #map node id to node GPS (intersections) #{Number:[QgsPoint]}
        self.nodes = {} #{Number: QgsPoints}
        self.links = {} #0~|E|-1 #Attribute
        self.arcs={} #map extended feature id to arc (start, end) #{Number:(Number,Number,QgsFeature)}
        self.graph = defaultdict(defaultdict) #{start:{end}} #{Number:{Number:Weight}}
        self.inverse_graph = defaultdict(defaultdict) #{end:{start}} #{Number:{Number:Weight}}
        #Xboundry[0] = min X Xboundry[1] = max X
        #Yboundry[0] = min Y Yboundry[1] = max Y
        self.Xboundary = [-1, -1]
        self.Yboundary = [-1, -1]
        
    def construct_edges(self):
        #Construct Initial Graph
        for feature in self.features:
            geom = feature.geometry()
            oneWay = feature.attribute("oneway")
            id = feature.id()
            points = list(geom.vertices())
            start = 2 * id
            end = 2 * id + 1
            if self.endNode <= end:
                self.endNode = end + 10;
            self.nodes[start] = points[0]
            self.nodes[end] = points[-1]
            maxspeed = feature.attribute("maxspeed")
            v = maxspeed if maxspeed != 0 else speedlimit[feature.attribute("fclass")]
            l = self.distance.measureLength(feature.geometry())
            self.graph[start][end] = [-1, l, v]
            self.inverse_graph[end][start] = [-1, l, v]
            self.arcs[start] = [start, end, feature]
            if(oneWay == 0 or oneWay == 'B'): #two-way
                self.graph[end][start] = [-1, l, v]
                self.inverse_graph[start][end] = [-1, l, v]
                self.arcs[end] = [end, start, feature]
            self.get_boundary(points[0])
            self.get_boundary(points[1])
        print(self.Xboundary, self.Yboundary)
        
    def get_boundary(self, point):
        x = point.x()
        y = point.y()
        if(self.Xboundary[0] == -1 or self.Xboundary[0] > x):
            self.Xboundary[0] = x
        if(self.Xboundary[1] == -1 or self.Xboundary[1] < x):
            self.Xboundary[1] = x
        if(self.Yboundary[0] == -1 or self.Yboundary[0] > y):
            self.Yboundary[0] = y
        if(self.Yboundary[1] == -1 or self.Yboundary[1] < y):
            self.Yboundary[1] = y

    def drawPath2(self, finalTrajectory, layername): #draw generated paths on a layer in QGIS
        self.linea = iface.addVectorLayer("LineString?crs=epsg:4326&field=id:int&field=start:int&field=end:int&field=length(m)&field=maxspeed(km/h):int&field=fftime(s)&field=carnumber:int&index=yes",layername,"memory")
        self.linea.startEditing()
        for linkid, number in finalTrajectory.items():
            s,t = self.links[linkid]
            feature = QgsFeature()
            feature.setGeometry(QgsGeometry.fromPolyline([self.nodes[s], self.nodes[t]]))
            w = self.graph[s][t]
            i = w[0]
            l = w[1]
            v = w[2]
            fftime = 3.6 * l / v
            feature.setAttributes([i, s, t, l, v, fftime, number])
            self.linea.addFeature(feature)
        self.linea.commitChanges()
        single_symbol_renderer = self.linea.renderer()
        symbol = single_symbol_renderer.symbols(QgsRenderContext())[0]  
        arrowSL = QgsArrowSymbolLayer()
        arrowSL.setHeadLength(3)
        arrowSL.setHeadThickness(2)
        arrowSL.setArrowWidth(0.1)
        arrowSL.setArrowStartWidth(0.3)
        arrowSL.setColor(QColor.fromRgb(225, 0, 0))
        symbol.appendSymbolLayer(arrowSL)
#        self.linea.triggerRepaint()
        iface.zoomToActiveLayer()

    def assign_linkid(self):
        linkid = 0
        for s, value in self.graph.items():
            for t in value:
                linkid = linkid + 1
                self.graph[s][t][0] = linkid
                self.inverse_graph[t][s][0] = linkid
                self.links[linkid] = (s, t)

    ##get cluster result for large graph
    ##result: if nodes (a1, a2, ..., an) are in one cluster (distance between each other is within threshold)
    ##result[a1] will be [a1, a2, ..., an], and all other result[ai] = [a1]
    def get_cluster(self, threshold):
        XSize = self.Xboundary[1] - self.Xboundary[0]
        grid_size = threshold * 0.0001 / 11.086400119993227
        XBase = math.ceil(XSize / grid_size + 20)
        grid = defaultdict(set)
        result = {}
        for nx, point in self.nodes.items():
            px = math.ceil((point.x() - self.Xboundary[0]) / grid_size) + 10
            py = math.ceil((point.y() - self.Yboundary[0]) / grid_size) + 10
            for index in self.get_index(XBase, px, py):
                grid[index].add(nx)
        for id in sorted(grid.keys()):
            for nx in sorted(grid[id]):
                if(result.__contains__(nx)):
                    continue
                flag = 0
                for ny in [ny for ny in grid[id] if result.__contains__(ny)]:
                    for nid in result[ny]:
                        if(self.get_distance(self.nodes[nid], self.nodes[nx]) > threshold):
                            flag = 1
                            break
                    if(flag==0):
                        result[result[ny][0]].append(nx)
                        result[nx] = [result[ny][0]]
                        flag = 1
                        break
                    else:
                        flag = 0
                if(flag == 0):
                    result[nx] = [nx]
        return result
        
    def check_cluster(self, result):
        flag = 0
        for id, value in result.items():
            if((len(value) == 1 and id not in result[value[0]]) or\
               (len(value) > 1 and value[0] != result[value[0]][0]) ):
                print("not valid", id, value, result[value[0]])
                flag = 1
        if flag: print("valid") 
        return

    def merge_edges(self, threshold): #remove all edges in a cluster and build edges between clusters
        #Merge Points
        result = self.get_cluster(threshold)
        self.check_cluster(result)
        print("get result")
        # print(result)
        for realEdgeId in self.arcs.keys():
            self.arcs[realEdgeId][0] = result[self.arcs[realEdgeId][0]][0]
            self.arcs[realEdgeId][1] = result[self.arcs[realEdgeId][1]][0]
        for id, value in result.items():
            boss = value[0]
            if(len(value) > 1):
                centerPoint = self.get_centroid(value)
                for i in range(1, len(value)):
                    s = value[i]
                    for t in self.graph[s]:
                        weight = self.graph[s][t]
                        if(self.inverse_graph[t].__contains__(s)):
                            self.inverse_graph[t].pop(s)                            
                        if(t not in value):
                            if(self.graph[boss].__contains__(t)):
                                if(weight[0]<self.graph[boss][t][0]):
                                    self.graph[boss][t] = weight                               
                            else:
                                self.graph[boss][t] = weight
                            self.inverse_graph[t][boss] = self.graph[boss][t]
                    if(self.graph.__contains__(s)):
                        self.graph.pop(s)
                    nt = value[i]
                    for ns in self.inverse_graph[nt]:
                        weight = self.inverse_graph[nt][ns]
                        if(self.graph[ns].__contains__(nt)):
                            self.graph[ns].pop(nt)                            
                        if(ns not in value):
                            if(self.inverse_graph[boss].__contains__(ns)):
                                if(weight[0]<self.inverse_graph[boss][ns][0]):
                                    self.inverse_graph[boss][ns] = weight                              
                            else:
                                self.inverse_graph[boss][ns] = weight
                            self.graph[ns][boss] = self.inverse_graph[boss][ns]
                    if(self.inverse_graph.__contains__(nt)):
                        self.inverse_graph.pop(nt)
                self.nodes[boss] = centerPoint
        for id, value in result.items():
            if(len(value) > 1):
                for i in range(1, len(value)):
                    if(self.nodes.__contains__(value[i])):
                        self.nodes.pop(value[i])

    def get_index(self, XBase, px, py): #return 8 neighbour grids
        center = XBase * px + py
        return [center - XBase - 1, center - XBase, center - XBase + 1,\
                center - 1, center, center + 1,\
                center + XBase - 1, center + XBase, center + XBase + 1]

    def get_index2(self, XBase, px, py): #return a grid given x,y coordinates
        return [XBase * px + py]

    def get_index3(self, XBase, px, py, level): #return 8i neighbour grids on the ith layer(level) 
        if(level == 1):
            center = XBase * px + py
            return [center - XBase - 1, center - XBase, center - XBase + 1,\
                    center - 1, center + 1,\
                    center + XBase - 1, center + XBase, center + XBase + 1]
        result = []
        cur = XBase * (px - level) + (py - level)
        for i in range(0, 2 * level):
            result.append(cur + i)
        cur = cur + 2 * level
        for i in range(0, 2 * level):
            result.append(cur + i * XBase)
        cur = cur + 2 * level * XBase
        for i in range(0, 2 * level):
            result.append(cur - i)
        cur = cur - 2 * level
        for i in range(0, 2 * level):
            result.append(cur - i * XBase)
        return result

    def punch_line(self, interval): #return holes(equidistant points) on a line(MultiLineString)
        result = []
        for realEdgeId, arc in self.arcs.items():
            feature = arc[2]
            geom = feature.geometry()
            points = list(geom.vertices())
            for i in range(1, len(points)):
                point1 = points[i-1]
                point2 = points[i]
                d = self.get_distance(point1, point2)
                n = math.ceil(d/interval)+5
                x1 = point1.x()
                y1 = point1.y()
                x2 = point2.x()
                y2 = point2.y()
                Xinterval = (x2-x1)/n
                Yinterval = (y2-y1)/n
                for j in range(1, n):
                    point = QgsPoint(x1 + j*Xinterval, y1 + j*Yinterval)
                    result.append((realEdgeId, point))
        return result

    #find nearest links given a point
    def get_nearest(self, flag, lot, lat, grid_size, XBase, grid, threshold):
        px = math.ceil((lot - self.Xboundary[0]) / grid_size) + 10
        py = math.ceil((lat - self.Yboundary[0]) / grid_size) + 10
        loc = XBase * px + py
        result = set() #link numbers
        new_result = {} #link numbers with two ends and distances between them
        point = QgsPoint(lot, lat)
        if flag==1:
            if grid[loc]:
                for candidate in grid[loc]:
                    dist = self.get_distance(point, candidate[1])
                    if(dist < threshold):
                        result.add(candidate[0])
            for i in range(1, 6):
                closeLoc = self.get_index3(XBase, px, py, i)
                for cl in closeLoc:
                    if grid[cl]:
                        for candidate in grid[cl]:
                            dist = self.get_distance(point, candidate[1])
                            if(dist < threshold):
                                result.add(candidate[0])

            for link in result:
                if(link < 0):
                    new_result[link] = (link, link)
                else:   
                    start = self.links[link][0]
                    end = self.links[link][1]
                    d1 = self.get_distance(point, self.nodes[start])
                    d2 = self.get_distance(point, self.nodes[end])
                    new_result[link] = (start, end)
        # print(lot, lat, new_result)
        return new_result

    def ComputeLinkGrid(self, interval, threshold): #put all holes into grids
        result = self.punch_line(interval)
        XSize = self.Xboundary[1] - self.Xboundary[0]
        self.grid_size = threshold * 0.0001 / 11.086400119993227
        self.XBase = math.ceil(XSize / self.grid_size + 20)
        grid_size = self.grid_size
        XBase = self.XBase
        self.link_grid = defaultdict(list)
        for realEdgeId, point in result:
            px = math.ceil((point.x() - self.Xboundary[0]) / grid_size) + 10
            py = math.ceil((point.y() - self.Yboundary[0]) / grid_size) + 10
            start = self.arcs[realEdgeId][0]
            end = self.arcs[realEdgeId][1]
            if(start == end):
                for index in self.get_index2(XBase, px, py):
                    id = -start
                    self.link_grid[index].append((id, point))
            else:
                for index in self.get_index2(XBase, px, py):
                    id = self.graph[start][end][0]
                    self.link_grid[index].append((id, point))

    def PreProcess(self, timeIntervel, startInterval, ODPair, inputDic, outputDic): #one-time setup
        programStartTime = datetime.now()

        folderIndex = 1;
        for origin, dest in ODPair:
            outputSubDic = outputDic + str(folderIndex) + '/'
            if not os.path.exists(outputSubDic):
                os.makedirs(outputSubDic)
            start = datetime(2014,5,6,5,0,0) #2014-05-06 5:00
            end = datetime(2014,5,6,9,0,0) #2014-05-06 9:00
            Minutes = timedelta(minutes=5) #sliding window size = 30min, step = 5min
            result = dict()
            endDict = math.floor((end - start) / Minutes)
            st = start
            for i in range(0, endDict): #read file, input raw data
                result[i] = pd.DataFrame(columns=["Car Id", "Date", "start", "end", "status", "lot", "lat"])
                se = st + Minutes
                print(inputDic)
                file_name = inputDic + str(st).replace(":", "-").replace(" ", "-") + "-" + str(se).replace(":", "-").replace(" ", "-") + ".csv"
                print("file, ", file_name)
                df = pd.read_csv(file_name)
                df["start"]=df.apply(lambda x: self.get_distance(origin, QgsPoint(x["lot"], x["lat"])), axis=1) #distance to origin
                df["end"]=df.apply(lambda x: self.get_distance(dest, QgsPoint(x["lot"], x["lat"])), axis=1) #distance to destination
                simpledf = pd.DataFrame(df, columns=["Car Id", "Date", "start", "end", "status", "lot", "lat"])
                print("cal dist succ takes seconds", (datetime.now() - programStartTime).total_seconds() )
                result[i] = simpledf.copy()
                st = st + Minutes
            st = start
            timeDict = math.floor(timeIntervel / Minutes)
            while(st + timeIntervel <= end): #write file, prepare empty output
                stDict = math.floor((st - start)/Minutes)
                tr = pd.DataFrame(columns=["Car Id", "Date", "start", "end", "status", "lot", "lat"])
                tr = result[stDict].copy()
                for i in range(stDict + 1, stDict + timeDict):
                    tempresult = pd.DataFrame(columns=["Car Id", "Date", "start", "end", "status", "lot", "lat"])
                    tempresult = result[i].copy()
                    # print(tempresult)
                    tr = tr.append(tempresult, ignore_index = True)
                tr = tr.sort_values(["Car Id", "Date"])
                outputfile = outputSubDic + str(st).replace(":", "-").replace(" ", "-") + "-" + str(st + timeIntervel).replace(":", "-").replace(" ", "-") + ".csv"
                tr.to_csv(outputfile)
                print("outputfile, ", outputfile)
                st = st + startInterval
            

    def NNDic(self, thresholdToOriginAndDest, thresholdLink, inputDic, outputDic):
        files= os.listdir(inputDic)
        for file in files:
            inputSubDic = inputDic + file + "/"
            outputSubDic = outputDic + file + "/"
            print("cal all ", inputSubDic)
            if os.path.exists(inputSubDic):
                if not os.path.exists(outputSubDic):
                    os.makedirs(outputSubDic)
                subFiles = os.listdir(inputSubDic)
                allEdgesFile = open(outputSubDic + "alledges", "w")
                for subFile in subFiles:
                    print("1")
                    fileName = inputSubDic + subFile
                    outputfile = outputSubDic + subFile
                    programStartTime = datetime.now()
                    if(subFile.split(".")[-1] != "csv"):
                        continue
                    print("NNJoin file: ", fileName)
                    self.NNJoin(thresholdToOriginAndDest, thresholdLink, fileName, outputfile)
                    print("cal takes ", (datetime.now() - programStartTime).total_seconds())
                
                allEdgesFile.write("%s\n" % self.allActiveEdges)

    def NNJoin(self, thresholdToOriginAndDest, thresholdLink, inputfile, outputfile, DuplicateThreshold = 10, withDraw = True):
        programStartTime = datetime.now()
        ## the input files are data segments after time slicing
        self.data = pd.read_csv(inputfile)
        print("read succ")
        print("read dataframe takes ", (datetime.now() - programStartTime).total_seconds())
 
        df = self.data
        print("cal dist succ takes ", (datetime.now() - programStartTime).total_seconds() )

        ## find all cars which pass by both the origin and the destination
        st1 = set(df[df["start"] <= thresholdToOriginAndDest]["Car Id"])
        st2 = set(df[df["end"] <= thresholdToOriginAndDest]["Car Id"])
        st = st1.intersection(st2)

        print("satisfied car", st)

        if(len(st) == 0):
            pathdf = pd.DataFrame(columns =  ["Car Id", "node sequence", "path sequence"])
            print("get results takes ", (datetime.now() - programStartTime).total_seconds())
            pathdf.to_csv(outputfile)
            return

        df = df[df["Car Id"].isin(st)]
        df["link"] = df.apply(lambda x: self.get_nearest(1, x["lot"], x["lat"], self.grid_size, self.XBase, self.link_grid, thresholdLink), axis=1).astype(object)

        
        pathdf = pd.DataFrame(columns =  ["Car Id", 
            "node sequence", "path sequence", "each fftime", "total fftime", "real time"])
        ## Start recovering trajectory
        withDraw = False # whether draw trajectory or not
        curNodeList = set()
        routeList = {}
        self.setCurId()
        self.assignRouteList(routeList, 0, 0, 0)
        curCarId = -1
        inRoad = False
        takePassenger = False
        havePassenger = False
        dropPassenger = False
        finalTrajectory = {}
        startTime = datetime(2014,5,6,5,0,0)
        endTime = datetime(2014,5,6,9,0,0)
        for index, row in df.iterrows():
            carId = row["Car Id"]
            if(carId != curCarId):
                curCarId = carId
                #print("car Id ", curCarId)
                inRoad = False #True if the point is between the origin and destination
                takePassenger = False #True if the car picks up a passenger
                havePassenger = False #True if the car is serving
                dropPassenger = False #True if the car drops off a passenger
                curNodeList = set()
                routeList = {}
                self.setCurId()
                self.assignRouteList(routeList, 0, 0, 0)
            if(row["start"] < thresholdToOriginAndDest): #if close to the origin
                inRoad = True
                if(row["status"] == 1 and not havePassenger):
                    takePassenger = True
            if(row["end"] < thresholdToOriginAndDest): #if close to the destination
                inRoad = False
                if(row["status"] == 1 and havePassenger):
                    dropPassenger = True
            if(dropPassenger): #the end of a trajectory
                nodePath = self.getPath(curNodeList, routeList) #get the node sequence
                #calculate free flow time, total free flow time and real travel time
                fftime = [0];
                for i in range(2, len(nodePath) - 1):
                    linkid = self.graph[nodePath[i-1]][nodePath[i]][0]
                    l = self.graph[nodePath[i-1]][nodePath[i]][1]
                    v = self.graph[nodePath[i-1]][nodePath[i]][2]
                    fftime.append(3.6 * l / v)
                    self.allActiveEdges.add(linkid)
                    if(finalTrajectory.__contains__(linkid)):
                        finalTrajectory[linkid] = finalTrajectory[linkid] + 1
                    else:
                        finalTrajectory[linkid] = 1
                linkPath = []
                for i in range(1, len(nodePath)):
                    linkPath.append(self.graph[nodePath[i-1]][nodePath[i]][0])
                fftime.append(0)
                totalFftime = sum(fftime)
                endTime = datetime.strptime(row["Date"], '%Y-%m-%d %H:%M:%S')
                realTime = (endTime - startTime).total_seconds()
                pathdf.loc[-1] = [carId, nodePath, linkPath, fftime, totalFftime, realTime]
                pathdf.index = pathdf.index + 1
                havePassenger = False
                dropPassenger = False
                curNodeList = set()
                routeList = {}
                self.setCurId()
                self.assignRouteList(routeList, 0, 0, 0)
            if inRoad and takePassenger: #the start of a trajectory
                havePassenger = True
                for linkId, value in row["link"].items(): #value: (start, end)
                    if(linkId < 0):
                        continue                                     
                    curNodeList.add(self.assignRouteList(routeList, self.assignRouteList(routeList, 0, value[0], 0), value[1], self.graph[value[0]][value[1]][1]))                
                    #routeList[0] = [0, value[0], 0]
                    #routeList[1] = [0, value[1], dist(value[0], value[1])] 
                    #add 1 to curNodeList 
                takePassenger = False
                startTime = datetime.strptime(row["Date"], '%Y-%m-%d %H:%M:%S')
                continue
            if havePassenger: #the mid of a trajectory
            	#expand layer by layer
                nextNodeList = self.getNextNodeList(row["link"], routeList, curNodeList, DuplicateThreshold)
                # self.printTestLinkSet(index, TestSet, row["link"], routeList, curNodeList, nextNodeList)
                if(nextNodeList == set()):
                    nextNodeList = self.getNextNodeList(row["link"], routeList, curNodeList, 0)
                    # self.printTestLinkSet(index, TestSet, row["link"], routeList, curNodeList, nextNodeList, "in null set")
                    if(nextNodeList != set()):
                        curNodeList = nextNodeList
                else:
                    curNodeList = nextNodeList

        ## write node sequences and link sequences into file
        pathdf = pathdf.sort_index()
        if withDraw: #draw trajectory
            fileName = inputfile.split('/')[-1]
            self.drawPath2(finalTrajectory, "result-" + fileName.split('.')[0]) 
        print("get results takes ", (datetime.now() - programStartTime).total_seconds())
        pathdf.to_csv(outputfile) #write file

    def printTestLinkSet(self, index, TestSet, links, routeList, curNodeList, nextNodeList, message = "\n"):
        if(index in TestSet):
            print(message)
            print("index, ", index, " links, ", links)
            print("cur, ",  [routeList[x] for x in curNodeList])
            print("next, ", [routeList[x] for x in nextNodeList])
            print("last level:", [ routeList[routeList[x][0]] for x in nextNodeList ])

    def getNextNodeList(self, links, routeList, curNodeList, DuplicateThreshold, index = -1):
        newNodeList = {} #map node id (value) to node tuple (point, value, distance)
        nextNodeList = set() #map curId+1 to (curId, value, distance)
        for linkId, value in links.items(): #value: (start, end)
            if(linkId < 0):
                continue
            for curNode in curNodeList:
                if(value[1] == routeList[curNode][1]):
                    if(value[0] == routeList[routeList[curNode][0]][1]):
                        if(not newNodeList.__contains__(value[1])):
                            newNodeList[value[1]] = curNode
                            nextNodeList.add(curNode)
                    continue
                visited = set()
                #find if there are duplicate nodes on the route within 10 hops
                findDuplicateNode = curNode
                for i in range(0, DuplicateThreshold):
                    findDuplicateNode = routeList[findDuplicateNode][0] #pred of curNode
                    visited.add(routeList[findDuplicateNode][1])
                #find the shortest path between the last node of current recovered route and the start of the canidate link
                path = self.shortest_path(routeList[curNode][1], value[0], visited) 
                if(visited.__contains__(value[1])): #if the end of the candidate link has been visited
                    continue
                path.append(value[1])
                if(path[0] < 0): #if no shortest path is found
                    continue
                #update the total length of the recovered route
                d = routeList[curNode][2] + self.graph[routeList[curNode][1]][path[0]][1]
                if(newNodeList.__contains__(path[0])):
                    point = newNodeList[path[0]]
                    if(routeList[point][2] > d):
                        routeList[point][0] = curNode
                        routeList[point][2] = d
                else:
                    point = self.assignRouteList(routeList, curNode, path[0], d)
                    #routeList[point+1] = [curNode, path[0], d]
                    newNodeList[path[0]] = point
                for i in range(1, len(path)):
                    d = routeList[point][2] + self.graph[routeList[point][1]][path[i]][1]
                    if(newNodeList.__contains__(path[i])):
                        p1 = newNodeList[path[i]]
                        if(routeList[p1][2] > d):
                            routeList[p1][0] = point
                            routeList[p1][2] = d
                        point = p1
                    else:
                        point = self.assignRouteList(routeList, point, path[i], d)
                        #routeList[point+1] = [point, path[i], d]
                        newNodeList[path[i]] = point
                nextNodeList.add(point) #add value[1] to nextNodeList
        return nextNodeList

    def getPath(self, curNodeList, routeList):
        CommonAncestor = -1
        for curNode in curNodeList:
            if(CommonAncestor < 0):
                CommonAncestor = curNode
            else:
                curPathNode = curNode
                while(curPathNode != CommonAncestor):
                    if(curPathNode > CommonAncestor):
                        curPathNode = routeList[curPathNode][0]
                    else:
                        CommonAncestor =  routeList[CommonAncestor][0]
        curPathNode = CommonAncestor
        path = [routeList[curPathNode][1]]
        while(curPathNode != 0):
            curPathNode = routeList[curPathNode][0]
            path.append(routeList[curPathNode][1])
        path.reverse()
        path.append(self.endNode)
        ## path is the node sequence
        return path

    def setCurId(self, startId = 0):
        self.curId = startId

    def assignRouteList(self, routeList, point, value, distance):
        routeList[self.curId] = [point, value, distance] #point: pred (id in routeList), value: node id (id in graph), distance: total length of the current route
        self.curId = self.curId + 1
        return self.curId - 1

    ## Run Dijkstra to find the missing nodes and links between origin and destination (not included)
    def shortest_path(self, origin, destination, visited):
        origin = int(origin)
        destination = int(destination)
        index = {}
        queue = OrderedDict()
        Rqueue = OrderedDict()
        queue[0] = origin
        Rqueue[origin] = 0
        if(origin == destination):
            return []
        while len(queue) > 0:
            distance, node = queue.popitem(False)
            Rqueue.pop(node)
            visited.add(node)
            if(node == destination):
                result = []
                cur = destination
                while(cur != origin):
                    result.append(cur)
                    cur = index[cur]
                result.reverse()
                return result
            for neighbour in self.graph[node].keys():
                if neighbour not in visited:
                    d = distance + self.graph[node][neighbour][1] + random.random()
                    if(Rqueue.__contains__(neighbour)):
                        if( Rqueue[neighbour] > d):
                            queue.pop(Rqueue[neighbour])
                            queue[d] = neighbour
                            Rqueue[neighbour] = d
                            index[neighbour] = node
                    else:
                        queue[d] = neighbour
                        Rqueue[neighbour] = d
                        index[neighbour] = node 
        return [-destination]


    def get_distance(self, point1, point2):
        point1 = QgsPointXY(point1)
        point2 = QgsPointXY(point2)
        return self.distance.measureLine(point1, point2)
    
    def get_centroid(self,cluster):
        curNodes = [self.nodes[point] for point in cluster]
        ln = len(curNodes)
        return QgsPoint(sum([node.x() for node in curNodes]) / ln, \
               sum([node.y() for node in curNodes]) / ln)
    
    def print(self):
        print("nodes number: ", len(self.nodes))
        print("arcs number: ", len(self.arcs))
        print("links number: ", sum([len(v) for i,v in self.graph.items()]))
        print("Xboundary: ", self.Xboundary)
        print("Yboundary: ", self.Yboundary)

workingPath = "/Users/crab_baby/Google Drive/IO Verification/Jane/"
## The layer testnet2 must be active when running this program in QGIS3
cg = Cgraph("studynetwork")
print("start constructing")
cg.construct_edges()
print("construct succ")
cg.print()
cg.merge_edges(30)
print("merge succ")
cg.assign_linkid()
print("assign succ")
cg.print()
thresholdToOriginAndDest = 500
thresholdLink = 50
interval = 10

ODPair = [(QgsPoint(114.26073427598737, 30.550508380517677), QgsPoint(114.31152839350551, 30.533107217977232))]
inputDic = workingPath + "result/"
midDic = workingPath + "midResult/"
outputDic = workingPath + "result2/"

## For each experiment, you can run PreProcess only one time to save your time
cg.PreProcess(timedelta(minutes=30), timedelta(minutes=5), ODPair, inputDic, midDic)
cg.ComputeLinkGrid(interval, thresholdLink)
cg.NNDic(thresholdToOriginAndDest, thresholdLink, midDic, outputDic)         
