{-
    Disclaimer!
    This turns out to be a poor implementation of Depth First Search (and thus Euler detection)
    in a functional language. Its runtime complexity is inflated by the O(n) complexity of Haskell's
    list index operator (!!), unlike the constant access time indexing in most imperative languages.
    While we minimize the use of the indexing operator, reliance on it in this context is remains an
    anti-pattern in Haskell.

    A much better approach to DFS involves defining our graphs inductively as proposed by Martin Erwig in his
    paper Inductive Graphs and Functional Graph Algorithms. Originally published in the Journal of Functional Programming,
    the paper is now available at http://web.engr.oregonstate.edu/~erwig/papers/InductiveGraphs_JFP01.pdf.

    Unfortunately, implementing Erwig's system from scratch is complex enough to, well, warrant a paper on the topic
    and is beyond the scope of this project. Alternatively, using the Functional Graph Library built on these principles
    trivializes the project. Accordingly, I have chosen to implement the naive algorithm while pointing out its
    shortcomings. 

    - Jude
-}

import Data.List

-- Since one of the major strengths of Haskell is its type system, we first define our
-- graph components
type Vertex     = Int
type Graph      = [[Vertex]]

-- Simple test data
amCycle :: Graph
amCycle = [[0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0]]
alCycle = adjMatrixToAdjList amCycle

amTrail :: Graph
amTrail = [[0, 1, 0, 0], [1, 0, 1, 0], [0, 1, 0, 1], [0, 0, 1, 0]]
alTrail = adjMatrixToAdjList amTrail

amNone :: Graph
amNone = [[0, 1, 1, 1], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
alNone = adjMatrixToAdjList amNone

amDisconnected :: Graph
amDisconnected = [[0, 0, 0, 0], [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0]]
alDisconnected = adjMatrixToAdjList amDisconnected

amDisordered :: Graph
amDisordered = [[0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]
alDisordered = adjMatrixToAdjList amDisordered

-- Because adjacency matrices lend themselves well towards indexed loops, they are better suited
-- for imperative programming than they are for functional programming.
-- To that end, we convert the matrix to adjacency lists.
adjMatrixToAdjList :: Graph -> Graph
adjMatrixToAdjList matrix = map (compressRow 0) matrix

-- Compresses a row of an adjacency matrix to an adjacency list
compressRow :: Vertex -> [Vertex] -> [Vertex]
compressRow _ []  = []
compressRow ndx (x:xs) = 
    if x > 0
    then ndx : (compressRow (ndx+1) xs)
    else compressRow (ndx+1) xs


-- Given an adjacency list, find the degree of the associated vertex
-- This is just an alias to make other functions more readable
degree :: [Vertex] -> Int
degree adjList = length adjList

-- Check to see if a single node has even degree based
-- on its adjacency list
evenDegree :: [Vertex] -> Bool
evenDegree adjList = even (length adjList) 

-- This is just the opposite of evenDegree, but is included
-- to make other functions more readable
oddDegree :: Integral a => [a] -> Bool
oddDegree adjList = odd (length adjList)

-- Check to see if an Euler cycle exists by seeing if
-- each entry in an adjacency matrix has even degree
-- Note that this does NOT consider the case of an unconnected graph
eulerCycleExists :: Graph -> Bool
eulerCycleExists adjMatrix = and (map evenDegree adjMatrix)

-- An alternate method to check whether an Euler cycle exists by seeing if
-- each entry in an adjacency matrix has even degree
-- Note that this does NOT consider the case of an unconnected graph
eulerCycleExists' :: Graph -> Bool
eulerCycleExists' adjMatrix = foldr (&&) True (map evenDegree adjMatrix)


-- Check to see if an Euler trail, but not an Euler cycle, exists
-- by checking to see if exactly two nodes have odd degree
-- Note that this does NOT consider the case of an unconnected graph
eulerTrailExists :: Integral a => [[a]] -> Bool
eulerTrailExists adjMatrix = length (filter oddDegree adjMatrix) == 2

--  Depth-first search
--  For a given vertex V:
--      for each vertex V' adjacent to V
--          if V' has not been visited, add it to the list
--          call DFS on any vertices adjacent to V'
-- dfs takes the graph to search, a list of visited vertices, and 
-- a list of discovered vertices
-- The initial call should look something like:
-- dfs graph [] [0]
-- to start at vertex 0.
-- TODO: Optimize by storing visited in a hash table rather than a list
dfs' :: Graph -> [Vertex] -> [Vertex] -> [Vertex] 
dfs' graph visited [] = reverse (visited)
dfs' graph visited (x:xs) =
    if elem x visited
    then dfs' graph visited xs
    else dfs' graph (x:visited) ((graph !! x) ++ xs) -- This is the problem line

-- Convenient wrapper for dfs' that starts from the 0 node
dfs :: Graph -> [Vertex]
dfs graph = dfs' graph [] [0] 

-- Check to see if the graph is connected bu running a depth first search on the graph
-- and seeing if the result contains every node
isConnected :: Graph -> Bool
isConnected graph = length graph == length (dfs graph)

-- Remove val from an adjacency matrix
removeFromRow :: [Vertex] -> Vertex -> [Vertex]
removeFromRow row val = filter (/= val) row

-- Remove targetValue from a row of a matrix with a specified index
removeFromSpecificRow :: Vertex -> Vertex -> (Int, [Vertex]) -> [Vertex]
removeFromSpecificRow targetIndex targetValue (ndx, row) = 
    if ndx == targetIndex
    then removeFromRow row targetValue
    else row

-- In a graph, take a list of vertices and remove the adjacency between targetVertex and vertexToRemove
removeFromGraph :: Graph -> Vertex -> Vertex -> Graph
removeFromGraph graph targetVertex vertexToRemove = 
    map (removeFromSpecificRow targetVertex vertexToRemove) indexedGraph
    where 
        indices = [0..((length graph) -1)]
        indexedGraph = zip indices graph


findEulerTrail :: Graph -> [Vertex]
findEulerTrail graph = findEulerTrail' graph start []
    where start = [head (head (filter (oddDegree ) graph))]

{-
    Take the first vertex V in the stack
    If it has degree 0, then add V to the answer and pop V
    Otherwise, take V', the first vertex adjacent to V
        remove the connection between V and V'
        put V' on the stack
    Repeat until the stack is empty
-}
findEulerTrail' :: Graph -> [Vertex] -> [Vertex] -> [Vertex]
-- If the stack is ever empty, we're done
findEulerTrail' graph [] trail = reverse trail -- We need to reverse because cons > append
findEulerTrail' graph (x:xs) trail =
    if degree (graph !! x) < 1 
    then findEulerTrail' graph xs (x : trail) -- Note that we cons to the FRONT of the trail
    else findEulerTrail' subsubgraph (removedVertex : (x:xs)) trail
    where 
        row = graph !! x
        removedVertex = head row -- The first edge coming from the first node in the stack  
        subgraph = removeFromGraph graph x removedVertex -- We need to remove the first thing adjacent to vertex x
        subsubgraph = removeFromGraph subgraph removedVertex x -- Now we need to remove the reciprocal adjacency

-- Seems like we should have a function wrapper to handle finding an Euler cycle
findEulerCycle :: Graph -> [Vertex]
findEulerCycle graph = findEulerTrail' graph [0] []

checkForCycle :: Graph -> [Vertex]
checkForCycle adjMatrix = 
    if (isConnected graph) && (eulerCycleExists graph)
    then findEulerCycle graph
    else []
    where graph = adjMatrixToAdjList adjMatrix

checkForTrail :: Graph -> [Vertex]
checkForTrail adjMatrix =
    if (isConnected graph) && (eulerTrailExists graph)
    then findEulerTrail graph
    else []
    where graph = adjMatrixToAdjList adjMatrix
