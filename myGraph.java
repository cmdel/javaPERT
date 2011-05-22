import java.util.*;

/**
 * This package implements a Project Evaluation and Review Technique simulation. 
 * 
 * 
 * @author Christos M Delivorias
 * @serial s0973777
 * @version 03/02/11
 */

/**
 * Graph Object.
 * 
 * <P>
 * This class constructs and instantiates a Graph to represent the PERT model.
 * The function of interest is {@link #criticalPath()}. This method implements a
 * Dynamic Programming algorithm to find the Graph's critical path. That is the
 * longest possible path in the graph and thus a measurement as to how long the
 * PERT process is expected to take before it finishes.
 * 
 * <P>
 * There was a plethora of algorithms for dynamic programming that were
 * implemented, both to test but also to see which ones actually worked. While
 * forward and backward propagation implemented a greedy approach and had some
 * success ( especially the backwards ), when it came to the example case102.dat
 * they could not handle the fact that there were multiple inputs to the end
 * node with a weight of 0, nor identify any hidden high cost edges in the
 * middle of the graph.
 * <P>
 * Two dynamic programming algorithms were then implemented. They were both
 * dealing with directed acyclic graphs (DAG) like PERT diagrams are. Dijkstra's
 * algorithm identified all the minimum cost paths, but once applied to maximum
 * cost paths it yielded no results. The first approach was inverting the weight
 * to take advantage of the algorithm's ability to find minimum values. An
 * approach to use a prioritised queue {@link PriorityQueue} yielded an
 * algorithm that performed in O(ElogV), E,N for Edges and Vertices, when the
 * simple implementation would yield O(V^2). The second option would've been to
 * use negative weights while still using a relaxation algorithm. Dijkstra
 * doesn't support negative weights so the final approach was the Bellman-Ford
 * algorithm. More on this at {@link #criticalPath()}.
 * 
 * <P>
 * This method has a small test case in the {@link #main(String[])} method to
 * test the implementation.
 * 
 */
public class myGraph {

	/* Here are the class variables, they store information about the Graph */
	private int maxVertices, maxEdges; // max dimensions of the Graph
	private int nVertices, nEdges; // current dimensions of the Graph
	private String[] vertices;
	private double edgeCost[];
	private int edgeFrom[];
	private int edgeTo[];
	Random r = new Random();
	private String startNode;
	private String endNode;
	double INF = Double.MAX_VALUE;

	// Fields necessary for Dijkstra's
	private final Set<String> settledV = new HashSet<String>();
	private final PriorityQueue<String> unSettledV;
	private final Map<String, Double> d = new HashMap<String, Double>();
	private final Map<String, String> pred = new HashMap<String, String>();

	/**
	 * Inner class to implement the {@link Comparator} class for the prioritised
	 * queue. The class overides the compare method and defines the comparisson
	 * criteria for each of the vertices added in the unsettled Queue. The
	 * benefit of this process is that by polling the queue it always returns
	 * the object with the smallest weight.
	 */
	private final Comparator<String> minDistanceComparator = new Comparator<String>() {

		@Override
		public int compare(String from, String to) {
			double result = getMinDistance(from) - getMinDistance(to);
			return (int) ((result == 0) ? from.compareTo(to) : result);
		}
	};

	/*
	 * These need to be set by the criticalPath method. The methods
	 * criticalPathLength and verticesCriticalPath depend on these being set
	 * correctly
	 */
	private int idxNextVertex[];
	private double lengthCriticalPath = 0.0;

	private boolean print; // to indicate if the class should print anything

	/* stuff for the critical path method */

	/**
	 * constructor that takes the maximal dimension of the Graph as argument
	 * 
	 * @param maxVertices
	 *            Maximum number of vertices
	 * @param maEdges
	 *            Maximum number of edges
	 */
	myGraph(int maxVertices, int maxEdges) {
		// remember passed parameters
		this.maxVertices = maxVertices;
		this.maxEdges = maxEdges;
		
		// set edge and vertex counters to 0
		nVertices = 0;
		nEdges = 0;

		// initialise all arrays now that we know the dimension
		vertices = new String[maxVertices];
		edgeCost = new double[maxEdges];
		edgeFrom = new int[maxEdges];
		edgeTo = new int[maxEdges];

		// do printing by default
		print = true;
		unSettledV = new PriorityQueue<String>(maxVertices,
				minDistanceComparator);

	}

	/** Switches off printing */
	public void quiet() {
		print = false;
	}

	/**
	 * Add a vertex to the Graph. Tests that the vertex has not been defined
	 * already and that the maximal dimension of the Graph is not exceeded
	 * 
	 * @param vert
	 *            vertex to be added
	 */
	public void addVertex(String vert) {
		// check that there is still space in the arrays
		if (nVertices >= maxVertices) {
			throw new IndexOutOfBoundsException("No space for more vertices");
		}

		// check whether vertex is known already
		boolean found = false;
		for (int i = 0; i < nVertices; i++) {
			if (vertices[i].equals(vert))
				found = true;
		}

		if (found) {
			System.out.println("GRAPH: vertex " + vert + " is already known");
		} else {
			// if not then put vertex in array and increase counter
			if (print)
				System.out.println("GRAPH: Add Vertex: " + vert);
			vertices[nVertices] = vert;
			nVertices++;
		}
	}

	/**
	 * Add an edge to the graph. Test that both vertices are defined and that
	 * there is space for another edge.
	 * 
	 * @param from
	 *            source vertex
	 * @param to
	 *            target vertex
	 * @param cost
	 *            cost/length of edge
	 * @exception IllegalArgumentException
	 *                thrown if one of the vertices does not exist
	 */
	public void addEdge(String from, String to, double cost) {
		int i1, i2;

		// find the indices of the start and end vertex in the vertex-array
		i1 = findVertex(from);
		i2 = findVertex(to);

		// check if there is space for more edges
		if (nEdges >= maxEdges) {
			throw new ArrayIndexOutOfBoundsException("No space for more edges");
		}

		if (print)
			System.out.println("GRAPH: Add Edge: " + from + " - " + to + " : "
					+ cost);

		// put edge information in arrays and increase edge counter
		edgeCost[nEdges] = cost;
		edgeFrom[nEdges] = i1;
		edgeTo[nEdges] = i2;
		nEdges++;
	}

	/**
	 * Change the cost of an existing edge. Check that the edge does indeed
	 * exist
	 * 
	 * @param vert1
	 *            source vertex
	 * @param vert2
	 *            target vertex
	 * @param cost
	 *            new cost/length of edge
	 * @exception IllegalArgumentException
	 *                thrown if one of the vertices does not exist or edge has
	 *                not been registered yet
	 */

	public void newCost(String vert1, String vert2, double cost) {
		int i1, i2, i;
		boolean found;

		// get the indices of the start and end vertex
		i1 = findVertex(vert1);
		i2 = findVertex(vert2);

		// search for the index of the edge in the edge array
		found = false;
		for (i = 0; i < nEdges; i++) {
			if (i1 == edgeFrom[i] && i2 == edgeTo[i]) {
				// if found change cost
				if (print)
					System.out.println("GRAPH: New Cost for edge: " + vert1
							+ " - " + vert2 + " : " + cost);
				edgeCost[i] = cost;
				found = true;
				// and stop the for loop
				break;
			}
		}

		// if not found throw an Exception
		if (!found) {
			throw new IllegalArgumentException("Edge " + vert1 + " - " + vert2
					+ " not in graph");
		}
	}

	/**
	 * Critical Path Method: calculates longest Path through the network Assumes
	 * that there is only one Finish node (i.e. with no edges leaving)
	 * 
	 * The method can assume that information about the graph is found in the
	 * class variables: String[] vertices; double edgeCost[]; int edgeFrom[];
	 * int edgeTo[];
	 * 
	 * The method needs to set idxNextVertex and lengthCriticalPath to the
	 * correct values
	 * 
	 * lengthCriticalPath: the length of the Critical Path, that is the longest
	 * path through the network terminating at the Finish Node.
	 * 
	 * idxNextVertex[i]: the index of the node following node-i on the longest
	 * path to the Finish Node.
	 */
	public void criticalPath() {

		// allocates the idxNextVertex array
		idxNextVertex = new int[nVertices];

		if (print)
			System.out.println("GRAPH: Find critical path");

		// Determine the start and end of the graph tree
		this.getStart();
		this.getEnd();

		setMinDistance(startNode, 0); // Begin from the start node and set its
										// distance to 0

		/**
		 * Run the Longest path dynamic programming algorithm. The rest of the
		 * non-conforming algorithms are commented out. Different algorithms
		 * were tested out for suitability. The Bellman-Ford was the one
		 * selected in the end.
		 */
		// runDijkstra(); 				// Can't handle longest distance with negative
										// weights. Doesn't produce optimal solution.
										// Works to define the minimum path.
		// runBackwardsPropagation(); 	// Can't handle an end node with all edges
										// to it being 0. Doesn't produce optimal solution.
		// runForwardsPropagation(); 	// Can't handle hidden large edges later in
										// the graph. Doesn't produce optimal solution.
		
		 runBellmanFord(); 				// The dynamic programming algorithm finally used 
	}

	/**
	 * Backwards propagating Bellman-Ford(BF) algorithm. The BellmanÐFord
	 * algorithm computes single-source shortest paths in a weighted digraph.
	 * BellmanÐFord runs in O(|V|á|E|) time, where |V| and |E| are the number of
	 * vertices and edges respectively. 
	 ****************************************************************************
	 ****************************************************************************
	 * procedure BellmanFord(list vertices, list edges, vertex source) 
	 * This implementation takes in a graph,
	 * represented as lists of vertices and edges, and modifies the vertices
	 * so that their distance and predecessor attributes store the shortest
	 * paths.
	 * 
	 * Step 1: 
	 * initialize graph for each vertex v in vertices: 
	 * 		if v is source
	 * 		then v.distance := 0 
	 * 		else v.distance := infinity 
	 * 		v.predecessor := null
	 * 
	 * Step 2: 
	 * relax edges repeatedly 
	 * 		for i from 1 to size(vertices)-1: 
	 * 		for each edge uv in edges: // uv is the edge from u to v 
	 * 			u := uv.source 
	 * 			v := uv.destination 
	 * 			if u.distance + uv.weight < v.distance: 
	 * 				v.distance := u.distance + uv.weight 
	 * 				v.predecessor := u
	 * 
	 * Step 3: 
	 * check for negative-weight cycles 
	 * 		for each edge uv in edges: 
	 * 			u := uv.source 
	 * 			v := uv.destination 
	 * 			if u.distance + uv.weight < v.distance:
	 * 				error "Graph contains a negative-weight cycle"
	 ****************************************************************************
	 ****************************************************************************
	 * 
	 * From http://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm
	 */
	private void runBellmanFord() {
		// the 'distance' array contains the distances from the main source to
		// all other nodes
		double[] distance = new double[nVertices];
		// at the start - all distances are initiated to infinity
		Arrays.fill(distance, INF);
		// the distance from the end vertex to itself is 0
		distance[findVertex(startNode)] = 0;
		// set the start nodes' predecessor
		pred.put(startNode, null);
		// Relaxing all edges for all vertices
		for (int i = 0; i < nVertices; ++i)
			// relax every edge in 'edges'
			for (int j = 0; j < nEdges; ++j) {
				if (distance[edgeFrom[j]] == INF)
					continue;
				double newDistance = distance[edgeFrom[j]] - edgeCost[j];
				if (newDistance < distance[edgeTo[j]]) {
					distance[edgeTo[j]] = newDistance;
					pred.put(vertices[edgeTo[j]], vertices[edgeFrom[j]]);
				}
			}
		// Check if there are any negative cycles. Benefit of the BF algorithm
		// Break if there are cycles and don't find a critical path for the
		// graph.
		for (int i = 0; i < nEdges; ++i)
			if (distance[edgeFrom[i]] != INF
					&& distance[edgeTo[i]] > distance[edgeFrom[i]]
							+ edgeCost[i]) {
				 if (print) System.out.println("Cycles detected!");
				return;
			}

		for (int i = 0; i < distance.length; ++i)
			if (distance[i] == INF)
				System.out.println("There's no path between " + startNode
						+ " and " + endNode);
		// this loop outputs the distances from the main source node to all
		// other nodes of the graph
		// for (int i = 0; i < distance.length; ++i)
		// if (distance[i] > lengthCriticalPath && distance[i] != INF)
		// lengthCriticalPath = distance[i];
		
		// Populate the path in the array that prints the critical path in the end
		populatePath(distance);
	}

	/**
	 * 
	 */
	private void runForwardsPropagation() {
		double currPath = 0.0;
		String curr = startNode;
		idxNextVertex[findVertex(endNode)] = -1;
		int best = 0;
		double largestPath = 0;
		while (curr != endNode) {
			largestPath = 0;
			for (int i = 0; i < nEdges; i++) {
				if (vertices[edgeFrom[i]] == curr) {
					double c = edgeCost[i] + currPath;
					if (c > largestPath) {
						largestPath = c;
						best = edgeTo[i];
					}
				}
			}
			idxNextVertex[findVertex(curr)] = best;
			curr = vertices[best];
			lengthCriticalPath += largestPath;
		}
	}

	/**
	 * 
	 */
	private void runBackwardsPropagation() {
		double currPath = 0.0;
		String curr = endNode;
		idxNextVertex[findVertex(endNode)] = -1;
		int best = 0;
		while (curr != startNode) {
			for (int i = 0; i < nEdges; i++) {
				if (vertices[edgeTo[i]] == curr) {
					double c = edgeCost[i] + currPath;
					if (c > lengthCriticalPath)
						lengthCriticalPath += c;
					idxNextVertex[edgeFrom[i]] = findVertex(curr);
					best = i;
				}
			}
			curr = vertices[edgeFrom[best]];
		}
	}

	/**
	 * 
	 */
	private void runDijkstra() {
		/********************************************************************
		 * This is Dijkstra's Algorithm for shortest path. The implementation
		 * here will invert the costs in order to find the longest (critical)
		 * path. Initialize d(best estimate) to infinity, ¹(predecessor for each
		 * node) and S(settled vertices), V(unsettled vertices) to empty.
		 * 
		 * d = ( ° ) ¹ = () S = V = ()
		 * 
		 * add s(ource vertex) to Q d(s) = 0
		 * 
		 * while V is not empty { u = extract-minimum(V) add u to S
		 * relax-neighbors(u) } relax-neighbors(u) { for each vertex v adjacent
		 * to u, v not in S { if d(v) > d(u) + [u,v] // a shorter distance
		 * exists { d(v) = d(u) + [u,v] ¹(v) = u add v to V } } }
		 * 
		 * extract-minimum(Q) { find the smallest (as defined by d) vertex in V
		 * remove it from V and return it }
		 ********************************************************************/
		String vert;
		// There are unsettled vertices run the algorithm
		while ((vert = extractMinDist()) != null) {
			if (vert == vertices[findVertex(endNode)])
				break;
			settledV.add(vert); // Since vert is the the smallest value of the
								// PriorityQueue it's added to the settled
								// vertices
			relaxNeighbors(vert); // Update the labels of the adjacent nodes to
									// vert
		}

		if (print)
			for (Map.Entry<String, String> vertex : pred.entrySet()) {
				System.out.println(vertex);

			}
		lengthCriticalPath = d.remove(endNode);
		populatePath2();
	}

	/**
	 * Populate the array with the path in order to print the critical path in the end
	 * @param distance Contains the distances from the main source to all other nodes
	 * 
	 */
	private void populatePath(double[] distance) {
		idxNextVertex[findVertex(endNode)] = -1; // Condition for the print loop
													// to finish on the last
													// node.
		String vertex = endNode;
		String p = "";
		while (true) {
			for (Map.Entry<String, String> previous : pred.entrySet()) {
				if (previous.getKey() == vertex) {
					double maxDist = INF;
					if (previous.getValue() != null) {
						if (vertices[findVertex(previous.getKey())] == vertex
								&& distance[findVertex(previous.getValue())] < maxDist) {
							maxDist = distance[findVertex(previous.getKey())];
							p = vertices[findVertex(previous.getValue())];
						}
					} else {
						// The startNode has been reached
						p = null;
						break;
					}
				}
				if (print)
					System.out.println("finished with predecessors");
			}
			int previous = 0;
			if (p != null) {
				// Get the weight of the previous edge
				double edgeC = 0;
				for (int i = 0; i < maxEdges; i++) {
					if (vertices[edgeFrom[i]] == p
							&& vertices[edgeTo[i]] == vertex)
						edgeC = edgeCost[i];
				}
				lengthCriticalPath += edgeC;
				previous = findVertex(p);
				idxNextVertex[previous] = findVertex(vertex);
				vertex = vertices[previous];
			} else
				break;
		}
		if (print)
			System.out.println("finished populating");
	}

	/**
	 * This is the path population for Dijkstra's algorithm
	 */
	private void populatePath2() {
		idxNextVertex[findVertex(endNode)] = -1; // Condition for the print loop
													// to finish on the last
													// node.
		String vertex = endNode;
		while (true) {
			String p = pred.get(vertex);
			int previous = 0;
			if (p != null) {
				previous = findVertex(p);
				idxNextVertex[previous] = findVertex(vertex);
				vertex = vertices[previous];
			} else
				break;
		}
	}

	/**
	 * Method for relaxing the neighbors for Dijkstra's algorithm. The 
	 * weights for the neighbors are recalculated and the edges relabeled.
	 * 
	 * @param vert the vertex whose neighbor's vertices need to be relabeled.
	 */
	private void relaxNeighbors(String vert) {
		for (int i = 0; i < vertices.length; i++) {
			if (vertices[edgeFrom[i]] == vert) { // Find all the indexes of the
													// current vertex
				if (!isSettled(vertices[edgeTo[i]])) { // If the adjacent vertex
														// isn't settled
					double shortestDist = getMinDistance(vert) + edgeCost[i]; // Calculate
																				// the
																				// updated
																				// shortest
																				// path
																				// to
																				// the
																				// adjacent
																				// vertex
					if (shortestDist < getMinDistance(vertices[edgeTo[i]])) { // If
																				// it
																				// is
																				// less
																				// than
																				// the
																				// adjacent
																				// vertex's
																				// current
																				// shortest
																				// path
						setMinDistance(vertices[edgeTo[i]], shortestDist); // Update
																			// the
																			// adjacen't
																			// vertex's
																			// distance
																			// with
																			// the
																			// new
																			// one.
						pred.put(vertices[edgeTo[i]], vert); // Add the adjacent
																// vertex to the
																// current
																// node's
																// predecessor's
					}
				}
			}
		}
	}

	/**
	 * Method for Dijkstra's algorithm. Checks if the node is part of the
	 * settled vertices.
	 * 
	 * @param vertex
	 *            the vertex to check
	 * @return a boolean true/false whether it is included in the settled
	 *         vertices set.
	 */
	private boolean isSettled(String vertex) {
		return settledV.contains(vertex);
	}

	/**
	 * Method for Dijkstra's algorithm. Set the desired minimum distance.
	 * 
	 * @param vertex
	 *            the vertex whose distance to change
	 * @param distance
	 *            the value of the new distance
	 */
	public void setMinDistance(String vertex, double distance) {
		unSettledV.remove(vertex); // so that we don't have duplicates in the
									// queue when updated with a newer distance
		d.put(vertex, distance);
		unSettledV.add(vertex); // Re-balance the queue with the new distance
	}

	/**
	 * Method for Dijkstra's algorithm. Gets the minimum distance. If it's not
	 * set yet, it return the algorithms requisite of a very large value
	 * (INFINITY).
	 * 
	 * @param from
	 *            minimum distance from this node onwards.
	 * @return a value of the weight for this node
	 */
	private double getMinDistance(String from) {
		Double dist = d.get(from);
		return (dist == null) ? Integer.MAX_VALUE : dist;
	}

	/**
	 * Method for Dijkstra's algorithm. Setters for the predecessors
	 * 
	 * @param vertex
	 *            the vertex whose predecessor to change
	 * @param predes
	 *            the new predecessor
	 */
	private void setPred(String vertex, String predes) {
		pred.put(vertex, predes);
	}

	/**
	 * Method for Dijkstra's algorithm. Getters for the predecessors
	 * 
	 * @param vertex
	 *            the vertex whose predecessor to get
	 * @return the predecessor of the vertex
	 */
	public String getPred(String vertex) {
		return pred.get(vertex);
	}

	/**
	 * Method for Dijkstra's algorithm. The method to request the smallest
	 * distance. The priority queue is polled for an item. That item will be the
	 * smallest one.
	 * 
	 * @return the name of the vertex with the smallest distance to.
	 */
	public String extractMinDist() {
		return unSettledV.poll();
	}

	/**
	 * returns a String giving a list of all the vertices on the critical path.
	 * Assumes that the array idxNextVertex has been set correctly
	 */
	public String verticesCriticalPath() {
		// Initialise the list with the name of the first vertex
		String list = vertices[0];
		int currentIdx = 0;

		// while there is a next vertex on the critical path
		while (idxNextVertex[currentIdx] >= 0) {
			currentIdx = idxNextVertex[currentIdx];
			// add the name of the current vertex to the list
			list += " - " + vertices[currentIdx];
		}
		return list;
	}

	/**
	 * return the length of the last computed critical path. Assumes that
	 * criticalPathLength has been set correctly by criticalPath
	 */
	public double criticalPathLength() {

		return lengthCriticalPath;
	}

	/** Prints the current Graph to the screen */
	public void print() {
		System.out.println("The current graph can have a maximum of "
				+ maxVertices + " vertices and " + maxEdges + " Edges.");
		System.out.println("Current dimensions are " + nVertices
				+ " vertices and " + nEdges + " Edges.");
		System.out.println("List of Vertices:");
		System.out.print("  ");
		for (int i = 0; i < nVertices; i++)
			System.out.print(vertices[i] + "  ");
		System.out.println();
		System.out.println("List of Edges:");
		for (int i = 0; i < nEdges; i++)
			System.out.println(vertices[edgeFrom[i]] + " - "
					+ vertices[edgeTo[i]] + " : Cost = " + edgeCost[i]);

	}

	/**
	 * This is just a test method that calls the critical path for a small
	 * example problem
	 */
	public static void main(String args[]) {
		myGraph graph = new myGraph(5, 10);
		graph.quiet();
		graph.addVertex("A");
		graph.addVertex("B");
		graph.addVertex("C");
		graph.addVertex("D");
		graph.addVertex("E");
		graph.addEdge("A", "B", 3.0);
		graph.addEdge("A", "C", 4.0);
		graph.addEdge("B", "C", 2.0);
		graph.addEdge("B", "D", 1.0);
		graph.addEdge("C", "E", 3.0);
		graph.addEdge("D", "E", 8.0);
		graph.criticalPath();
		System.out.println("Critical Path length: "
				+ graph.criticalPathLength());
		System.out.println("Critical Path: " + graph.verticesCriticalPath());
	}

	/**
	 * Method to determine the end node of the graph.
	 * The only node with edges arriving but not leaving
	 * will be the terminal node.
	 */
	private void getEnd() {
		for (int i = 0; i < vertices.length; i++) {
			int from = 0;
			if (vertices[i] != null)
				from = findVertex(vertices[i]);
			for (int j = 0; j < edgeFrom.length; j++) {
				if (edgeFrom[from] != from)
					endNode = vertices[i];
			}
		}
		if (print)
			System.out.println(endNode);
	}

	/**
	 * The assumption is made that the first node in the file
	 * will be the starting node. The problem is that given the
	 * array index of the start node has the same value as the 
	 * value used to fill the instantiated array (i.e. 0).
	 */
	private void getStart() {
		startNode = vertices[0];
		if (print)
			System.out.println(startNode);
	}

	/**
	 * Helper method that finds the index of a vertex given its name
	 * 
	 * @param vertex
	 *            name of a vertex in the graph
	 * @return index of this vertex in the vertices array
	 */
	private int findVertex(String vertex) {
		int i1 = -1;
		boolean found = false;

		// scan through all vertices already known
		for (int i = 0; i < nVertices; i++) {
			if (vertices[i].equals(vertex)) {
				// if found the correct one => remember and stop the loop
				found = true;
				i1 = i;
				break;
			}
		}

		// if not found throw an exception
		if (!found) {
			throw new IllegalArgumentException("Vertex " + vertex
					+ " not in graph");
		}

		// else return the index
		return i1;
	}

	/**
	 * @return the startNode
	 */
	public String getStartNode() {
		return startNode;
	}

	/**
	 * @param startNode
	 *            the startNode to set
	 */
	public void setStartNode(String startNode) {
		this.startNode = startNode;
	}

	/**
	 * @return the endNode
	 */
	public String getEndNode() {
		return endNode;
	}

	/**
	 * @param endNode
	 *            the endNode to set
	 */
	public void setEndNode(String endNode) {
		this.endNode = endNode;
	}

}
