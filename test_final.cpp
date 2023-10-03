/*
 * HybridAutomata.cpp
 *
 *  Created on: 09-Jul-2014
 *      Author: amit
 */

#include <core/hybridAutomata/hybridAutomata.h>
#include "z3++.h"
#include <fstream>
#include <string>

using namespace std;

hybrid_automata::hybrid_automata() {
	dimension = 0;
}

hybrid_automata::hybrid_automata(std::map<int, location::ptr>& list_locs, location::ptr init_loc,
		int dim) {
	list_locations = list_locs;	//assigning a map to another map
	initial_loc = init_loc;
	dimension = dim;
}

location::ptr hybrid_automata::getInitialLocation() const {
	return initial_loc;
}

void hybrid_automata::addInitialLocation(location::ptr& initLoc) {
	initial_loc = initLoc;
}

void hybrid_automata::setInitialLoc(int loc_id)
{
	initial_loc = list_locations[loc_id];

}

location::const_ptr hybrid_automata::getLocation(int Loc_Id) const {
	assert(list_locations.count(Loc_Id)!=0);
	return list_locations.at(Loc_Id);
}


location::ptr hybrid_automata::getLocationNew(int Loc_Id) {
	assert(list_locations.count(Loc_Id)!=0);
	return list_locations.at(Loc_Id);
}


/* returns the location from the list of locations with locName */
location::const_ptr hybrid_automata::getLocation(string locName) const {

	std::map<int, location::ptr>::const_iterator locMapIter;

	for(locMapIter = list_locations.begin();locMapIter!=list_locations.end(); locMapIter++){
		std::pair<int, location::ptr> map_elem = *locMapIter;
		location::const_ptr l = this->getLocation(map_elem.first);
		string name = l->getName();
		if(locName.compare(name)==0)
			return l;
	}
	throw std::runtime_error("hybrid_automata: getLocation: No location with the asked location name\n");
}

int hybrid_automata::getDimension() const {
	return dimension;
}

void hybrid_automata::setDimension(int dim) {
	this->dimension = dim;
}

void hybrid_automata::addMappedLocationsList(std::map<int, location::ptr>& mapped_location_list){
	list_locations = mapped_location_list;
}
void hybrid_automata::addLocation(location::ptr& loc){
	int key = loc->getLocId();
	list_locations[key] = loc;	//storing the loc with the proper loc_id as the key
}

std::list<structuralPath::ptr> hybrid_automata::getStructuralPaths(unsigned int forbidden_loc_id, unsigned int depth)
{
	std::list<structuralPath::ptr> path_list; // It is empty here.

	unsigned int srcLoc = getInitialLocation()->getLocId();
	unsigned int destLoc = forbidden_loc_id;
	path_list = findAllPaths(srcLoc, destLoc, depth);

	return path_list;
}

unsigned int hybrid_automata::satEnumPaths(unsigned int forbidden_loc_id, unsigned int depth)
{

	location::ptr source_ptr = getInitialLocation();
	int u = source_ptr->getLocId();
	unsigned int v = forbidden_loc_id;
	unsigned int bound = depth;    // bound = # locations in a path.

	z3::context c;
	unsigned int count1 = 0;
	
	for (unsigned int k = 0; k < bound; k++)    
	{						

		// INIT Step
		z3::expr exp1 = c.bool_const("exp1");
		string arr = "v" + to_string(u)+"_"+ "0";
		unsigned int l = arr.length();
		char array[l];
		for (unsigned int i = 0 ; i < l; i++)
			array[i] = char(arr[i]);
		z3::expr x = c.bool_const(array);
		exp1 = x;
		for(auto it = list_locations.begin(); it != list_locations.end(); it++)
		{
			arr = "v" + to_string(it->first)+"_"+ "0";
			l = arr.length();
			char array1[l];
			for (unsigned int i = 0 ; i < l; i++)
				array1[i] = char(arr[i]);
			if (it->first != u)
			{
				z3::expr x1 = c.bool_const(array1);
				exp1 = (exp1 && !(x1));
			}
		}				   					
		z3::solver s(c);
		s.add(exp1);

		// NEXT Step

		z3::expr exp2 = c.bool_const("exp2");
		z3::expr exp22 = c.bool_const("exp22");
		if(k == 0)   
		{
			for (unsigned int i =0; i <= k; i++)   
			{
			
				for (auto it = list_locations.begin(); it != list_locations.end(); it++)
				{
					auto neighbor_nodes = it->second->getOutGoingTransitions();			
					arr = "v"+ to_string(it->first)+"_"+ to_string(i);
					l = arr.length();
					char array2[l];
					for (unsigned int j = 0 ; j < l; j++)
						array2[j] = char(arr[j]);
					z3::expr x2 = c.bool_const(array2);
					exp2 = x2;
					z3::expr exp2a = c.bool_const("exp2a");
					unsigned int count = 1;
					for (auto it2 = neighbor_nodes.begin(); it2 != neighbor_nodes.end(); it2++)
					{
						transition::ptr trans_ptr = *(it2);
						unsigned int loc_id = trans_ptr->getDestinationLocationId();
						arr = "v" + to_string(loc_id) +"_"+ to_string(i+1);
						l = arr.length();
						char array2[l];
						for (unsigned int j = 0 ; j < l; j++)
							array2[j] = char(arr[j]);
						z3::expr x2 = c.bool_const(array2);
						if(count == 1)
						{
							exp2a = x2;
						}
						if(count >= 2)
						{	
							exp2a = (exp2a || x2);
						}
						count++;
					}
					exp22 = implies(exp2, exp2a);
					s.add(exp22);
				}
			} 						
		}
		if(k >= 1)   
		{
			for (unsigned int i =0; i <= k-1; i++)   
			{		
				for (auto it = list_locations.begin(); it != list_locations.end(); it++)
				{
					auto neighbor_nodes = it->second->getOutGoingTransitions();			
					arr = "v"+ to_string(it->first)+"_"+ to_string(i);
					l = arr.length();
					char array2[l];
					for (unsigned int j = 0 ; j < l; j++)
						array2[j] = char(arr[j]);
					z3::expr x2 = c.bool_const(array2);
					exp2 = x2;
					z3::expr exp2a = c.bool_const("exp2a");
					unsigned int count = 1;
					for (auto it2 = neighbor_nodes.begin(); it2 != neighbor_nodes.end(); it2++)
					{
						transition::ptr trans_ptr = *(it2);
						unsigned int loc_id = trans_ptr->getDestinationLocationId();
						arr = "v" + to_string(loc_id) +"_"+ to_string(i+1);
						l = arr.length();
						char array2[l];
						for (unsigned int j = 0 ; j < l; j++)
							array2[j] = char(arr[j]);
						z3::expr x2 = c.bool_const(array2);
						if(count == 1)
						{
							exp2a = x2;
						}
						if(count >= 2)
						{	
							exp2a = (exp2a || x2);
						}
						count++;
					}
					exp22 = implies(exp2, exp2a);
					s.add(exp22);
				}
			} 	
		}						

		//EXCLUDE
		z3::expr exp3 = c.bool_const("exp3");
		z3::expr exp33 = c.bool_const("exp33");
		for (unsigned int i =0; i <= k; i++)
		{
			for(auto it1 = list_locations.begin(); it1 != list_locations.end(); it1++)
			{
				string arr = "v" + to_string(it1->first)+"_" + to_string(i);
				unsigned int l = arr.length();
				char array[l];
				for (unsigned int ii = 0 ; ii < l; ii++)
					array[ii] = char(arr[ii]);
				z3::expr x = c.bool_const(array);
				exp3 = x;
				z3::expr exp31 = c.bool_const("exp31");
				unsigned int count = 0;
				for(auto it2 = list_locations.begin(); it2 != list_locations.end(); it2++)
				{
					arr = "v" + to_string(it2->first)+"_"+ to_string(i);
					l = arr.length();
					char array1[l];
					for (unsigned int ii = 0 ; ii < l; ii++)
						array1[ii] = char(arr[ii]);
					if (it2->first != it1->first)
					{
						z3::expr x1 = c.bool_const(array1);
						if(count == 0)
						{
							exp31 = !(x1);
						}
						if(count >= 1)
						{	
							exp31 = (exp31 && !(x1));
						}
						count++;
					}
				}
				exp33 = implies(exp3, exp31);	
				s.add(exp33);
			}
		}						//End of Exclude Constraint.

		//TARGET
		z3::expr exp4 = c.bool_const("exp4");
		arr = "v" + to_string(v)+"_" + to_string(k);
		l = arr.length();
		char array13[l];
		for (unsigned int i = 0 ; i < l; i++)
			array13[i] = char(arr[i]);
		z3::expr x13 = c.bool_const(array13);
		exp4 = x13;						
		s.add(exp4);
							

		
		//Negation
		int count = 1;
		while(true)
		{
			if (s.check() == z3::sat)
			{	
				z3::model m = s.get_model();
				unsigned int w = m.size();
				z3::expr exp = c.bool_const("exp");
				int co = 0;
				for (unsigned int i = 0; i < w; i++)
				{
					z3::func_decl v1 = m[i];
					assert(v1.arity() == 0);
					arr = v1.name().str();
					l = arr.length();
					char array16[l];
					for (unsigned int j = 0 ; j < l; j++)
						array16[j] = char(arr[j]);
					z3::expr x15 = c.bool_const(array16);
					if(co == 0)
					{
						exp = (x15 != m.get_const_interp(v1));
					}
					if(co >= 1)
					{	
						exp = (exp || (x15 != m.get_const_interp(v1)));
					}
					co++;
				}
				s.add(exp);
				count++;
			}
			else
				break;
		}	
	count1 += --count;

	}
	return count1;
}

void hybrid_automata::printPath(vector<int>& path) {
	int size = path.size();
	for (int i = 0; i < size; i++)
		cout << path[i] << " ";
	cout << endl;
}

std::list<structuralPath::ptr> hybrid_automata::findAllPaths(int src, int dst, int depthBound) {
	std::list<structuralPath::ptr> allStructralPaths;

	std::pair<vector<int>, vector<transition::ptr> > pathDS;//pair of (vector of locIDs, vector of transIDs)
	queue<std::pair<vector<int>, vector<transition::ptr> > > q;

	// path vector to store the current path
	vector<int> path;
	path.push_back(src);
	pathDS.first = path;
	vector<transition::ptr> trans;
	pathDS.second = trans;
	q.push(pathDS);

	while (!q.empty()) {
		pathDS = q.front();
		q.pop();
		int last = pathDS.first[pathDS.first.size() - 1];
		if (last == dst) {
			//std::cout << " Solution path: ";
			//printpath(pathDS.first);
			std::list<location::const_ptr> path_locations;
			for (unsigned int i = 0; i < pathDS.first.size(); i++) {
				path_locations.push_back(getLocation(pathDS.first[i]));
			}
			std::list<transition::ptr> path_transitions;
			for (unsigned int i = 0; i < pathDS.second.size(); i++) {
				path_transitions.push_back(pathDS.second[i]);
			}
			structuralPath::ptr solutionPath = structuralPath::ptr(new structuralPath(path_locations, path_transitions));
			allStructralPaths.push_back(solutionPath);
			//Disable instruction continue to avoid repeated bad location (applicable for discrete systems)
			//continue;	//avoiding traversing further from here: bad location not repeated (applicable for hybrid systems)
		}
		// traverse to all the nodes connected to
		// current node and push new path to queue
		//std::cout<<"Last loc id: "<<last<<endl;
		location::const_ptr lastLoc = getLocation(last); //Note:: todo take care if last does not exist (if error occurs)
		std::list<transition::ptr> allOutTrans = lastLoc->getOutGoingTransitions();
		std::list<transition::ptr>::iterator it;
		for (it = allOutTrans.begin(); it != allOutTrans.end(); it++) {
			// if (isNotVisited(g[last][i], path)) {    //enable this if to avoid Cycle
			vector<int> newpath(pathDS.first);	//copy constructor
			newpath.push_back((*it)->getDestinationLocationId());
			//int locId = (*it)->getDestinationLocationId();
			//std::cout<<"Destination Loc is: "<<locId<<endl;
			//newpath.push_back(locId);
			vector<transition::ptr> newtrans(pathDS.second);	//copy constructor
			//int transId = (*it)->getTransitionId();
			//std::cout<<"Transition is: "<<transId<<endl;
			//string lstr = (*it)->getLabel();
			//std::cout<<lstr<<endl;
			newtrans.push_back((*it));
			int depthExplored = newpath.size();    //Size of the path
			if (depthExplored == (depthBound+1))	//Allows path of length depthBound but not (depthBound+1)
				break;
			std::pair<vector<int>, vector<transition::ptr> > new_pathDS;
			new_pathDS.first = newpath;
			new_pathDS.second = newtrans;
			q.push(new_pathDS);
			//}
		}
	}
	return allStructralPaths;
}


/*void hybrid_automata::getGraph() {
    int numLocations = getTotalLocations();
    std::cout<<numLocations<<endl;
    // Initialize an with all zeros
    math::matrix<int> adjacencyMatrix(numLocations, numLocations, 0);

    // Iterate through transitions and populate the adjacency matrix
    std::map<int, location::ptr> allLocations = getAllLocations();
    for (const std::pair<int, location::ptr>& locationPair: allLocations) {
        int sourceLocationId = locationPair.first;
        location::ptr sourceLocation = locationPair.second;

        // Get the list of outgoing transitions from the source location
        std::list<transition::ptr> outgoingTransitions = sourceLocation->getOutGoingTransitions();

        // Iterate through the outgoing transitions
        for (const transition::ptr& transitionPtr : outgoingTransitions) {
            int destinationLocationId = transitionPtr->getDestinationLocationId();

            // Populate the adjacency matrix with 1 to indicate a connection
            adjacencyMatrix(sourceLocationId, destinationLocationId) = 1;
        }
    }

    //hybrid_automata::printGraph(adjacencyMatrix);
    std::cout << "Adjacency Matrix:\n";
       for (int i = 0; i < numLocations; ++i) {
           for (int j = 0; j < numLocations; ++j) {
               std::cout << adjacencyMatrix(i, j) << "\t";
           }
           std::cout << "\n";
       }
    //return adjacencyMatrix;
}*/




void hybrid_automata::printGraph(const math::matrix<int>& mat) {
    // Get the dimensions of the matrix
    size_t numRows = mat.size1();
    size_t numCols = mat.size2();

    // Iterate through the rows and columns and print each element
    for (size_t i = 0; i < numRows; i++) {
        for (size_t j = 0; j < numCols; j++) {
            std::cout << mat(i, j) << "\t"; // Assuming tab separation for clarity
        }
        std::cout << "\n"; // Start a new line for the next row
    }
}


/*math::matrix hybrid_automata::getGraph() {
//void hybrid_automata::getGraph(){

//location::ptr initial_locId = getInitialLocation();   
//std::list<transition::ptr> allOutTrans = initial_locId->getOutGoingTransitions();   
	std::map<int, location::ptr> all_locations_list = getAllLocations();

	std::map<int, location::ptr>::iterator it;
	for (it = all_locations_list.begin();
			it != all_locations_list.end(); it++) {

		std::list<transition::ptr> allOutTrans = (*it).second->getOutGoingTransitions();
		unsigned int srcLocId = (*it).second->getLocId();
		std::cout << "Source location is: " << srcLocId << endl;
		std::cout << "Transitions are: ";
		for (std::list<transition::ptr>::iterator it1 = allOutTrans.begin(); it1 != allOutTrans.end(); it1++) {
			int transId = (*it1)->getTransitionId();
			std::cout << transId << " ";
		}
		std::cout<<endl;
return math::matrix();
}*/

math::matrix<int> hybrid_automata::getGraph() {
    int numLocations = getTotalLocations();
    std::cout << "Number of Locations: " << numLocations << std::endl;

    // Initialize an adjacency matrix with all zeros
    math::matrix<int> adjacencyMatrix(numLocations, numLocations, 0);

    // Iterate through transitions and populate the adjacency matrix
    std::map<int, location::ptr> allLocations = getAllLocations();
    for (const std::pair<int, location::ptr>& locationPair : allLocations) {
        int sourceLocationId = locationPair.first;
        location::ptr sourceLocation = locationPair.second;

        // Get the list of outgoing transitions from the source location
        std::list<transition::ptr> outgoingTransitions = sourceLocation->getOutGoingTransitions();

        // Iterate through the outgoing transitions
        for (const transition::ptr& transitionPtr : outgoingTransitions) {
            int destinationLocationId = transitionPtr->getDestinationLocationId();

            // Adjust indices to match the matrix's zero-based indexing
            int adjustedSourceId = sourceLocationId - 1;
            int adjustedDestId = destinationLocationId - 1;

            // Check if adjusted indices are within the valid range
            if (adjustedSourceId >= 0 && adjustedSourceId < numLocations &&
                adjustedDestId >= 0 && adjustedDestId < numLocations) {
                // Populate the adjacency matrix with 1 to indicate a connection
                adjacencyMatrix(adjustedSourceId, adjustedDestId) = 1;
            }
            else {
                std::cerr << "Invalid location IDs: " << sourceLocationId << ", " << destinationLocationId << std::endl;
            }
        }
    }
    return adjacencyMatrix;
}

typedef boost::adjacency_matrix<boost::directedS, int> BoostAdjacencyMatrix;
BoostAdjacencyMatrix hybrid_automata::bglGraph(const math::matrix<int>& adjacencyMatrix){
	//directed graph represented as adjacency matrix
    int numVertices = adjacencyMatrix.size1();

	//instantiate boost graph library adjacency matrix
	BoostAdjacencyMatrix bglAdjacencyMatrix(numVertices);

	//Populate BGL adjacency matrix using values from existing adjacency matrix
	for (int i = 0; i < numVertices; ++i) {
	    for (int j = 0; j < numVertices; ++j) {
	    	if (adjacencyMatrix(i, j) != 0) {
	    	            boost::add_edge(i, j, bglAdjacencyMatrix);
			}
	    }
	}

	 boost::print_graph(bglAdjacencyMatrix);
	return bglAdjacencyMatrix;
}

typedef boost::graph_traits<BoostAdjacencyMatrix>::vertex_descriptor Vertex;

const char* getColorName(boost::default_color_type color) {
    switch (color) {
        case boost::white_color: return "white";
        case boost::gray_color: return "gray";
        case boost::black_color: return "black";
        default: return "unknown";
    }
}

struct AllPathsVisitor : public boost::default_dfs_visitor {
		std::vector<Vertex> current_path_;
	    std::map<Vertex, int> current_path_count_; // Store visit counts for each vertex
public:
   std::set<std::vector<Vertex>> all_paths_set_; // Use a set to store unique paths
	    Vertex start_vertex_;
	    Vertex destination_vertex;
	    boost::default_color_type* color_map_; // Color map to manage the visited status of the vertices
	    int max_depth;
	    int path_no = 0;

	    AllPathsVisitor(Vertex start, Vertex destination, boost::default_color_type* color_map, int max_depth)
	        : start_vertex_(start), destination_vertex(destination), color_map_(color_map), max_depth(max_depth) {
	        current_path_.push_back(start_vertex_);
	        current_path_count_[start_vertex_] = 1;
	    }
	    void discover_vertex(Vertex u, const BoostAdjacencyMatrix& g) {
	    	 std::cout << "Vertex dv " << u << " color: " << getColorName(color_map_[u]) << std::endl;


	        if (current_path_.size() > max_depth) { // Repetition limit as necessary
	        	std::cout<< "mark3" <<std::endl;

	        	return;
			}
	        // Reset the vertex to allow for its repetition in cycles
	        put(color_map_, u, boost::white_color);

	    	if (!current_path_.empty()) {	//If the path is not empty and there's no valid edge transition from the last vertex in the current path to this vertex,
	            if (!boost::edge(current_path_.back(), u, g).second) {
		        	std::cout<< "mark2" <<std::endl;

	            	return;  // If there's no valid transition from the last vertex in current path to this vertex
	            }
	        } else if (u != start_vertex_) {
	        	std::cout<< "mark" <<std::endl;
	            return;  // Only paths starting from the desired starting vertex
	        }

	        // Add vertex to current path and update its visit count
	        current_path_.push_back(u);
	        current_path_count_[u]++;


//	        if (current_path_.size() > max_depth || current_path_count_[u] > 1) { // Repetition limit as necessary
//				return;
//			}

	        // Logic to check if a vertex has been visited too many times
//	        if (current_path_count_[u] > 1 || current_path_.size() > max_depth) { // Repetition limit as necessary
//	            return;
//	        }


	        std::cout << "Discovering vertex: " << u << " with color: " << getColorName(color_map_[u]) << std::endl;
	    }

    void examine_edge(const boost::graph_traits<BoostAdjacencyMatrix>::edge_descriptor& e, const BoostAdjacencyMatrix& g) {
        Vertex u = source(e, g);
        Vertex v = target(e, g);
//        std::cout << "Examining edge: " << u << " -> " << v << std::endl;
        std::cout << "Vertex " << u << " color: " << getColorName(color_map_[u]) << std::endl;
        std::cout << "Vertex " << v << " color: " << getColorName(color_map_[v]) << std::endl;

    }

    void tree_edge(const boost::graph_traits<BoostAdjacencyMatrix>::edge_descriptor& e, const BoostAdjacencyMatrix& g) {
            Vertex v = target(e, g);
            Vertex u = source(e, g);

            std::cout << "Vertex  te " << u << " color: " << getColorName(color_map_[u]) << std::endl;
			std::cout << "Vertex te " << v << " color: " << getColorName(color_map_[v]) << std::endl;

            if (v == destination_vertex && current_path_.size() + 1 <= max_depth) {

//            if (v == destination_vertex) {
                bool inserted;
                tie(std::ignore, inserted) = all_paths_set_.insert(current_path_);  // inserting the path. The 'inserted' will be false if the path was already present.
                if (inserted) {
                	path_no++;
                    std::cout << "Unique Path: "<<path_no<<" ";
                    for (Vertex vertex : current_path_) {
                        std::cout << vertex << "->";
                    }
                    std::cout << v << std::endl;
                }
            }
        }

    void back_edge(const boost::graph_traits<BoostAdjacencyMatrix>::edge_descriptor& e, const BoostAdjacencyMatrix& g) {
        Vertex v = target(e, g);
        Vertex u = source(e, g);
        // Encounter a back edge indicating a cycle. Reset the target vertex color to allow revisiting.
          put(color_map_, v, boost::white_color);
        if (!boost::edge(u, v, g).second) {
//            std::cout << "Invalid transition from " << u << " to " << v << std::endl;
            return;  // Skip the invalid transition.
        }


        std::cout << "Encountered a back edge from " << u << " to " << v << std::endl;
    }

    void finish_vertex(Vertex u, const BoostAdjacencyMatrix& g) {
    	 std::cout << "Vertex fv" << u << " color: " << getColorName(color_map_[u]) << std::endl;

    	 if (current_path_count_[u] > 0) {
			put(color_map_, u, boost::white_color);
			current_path_count_[u]--; // Decrement visit count
		}
		if (!current_path_.empty()) {
			current_path_.pop_back();
		}

		std::cout << "Vertex fv" << u << " color: " << getColorName(color_map_[u]) << std::endl;

		for (Vertex vertex : current_path_) {
			std::cout << vertex;
		}
		std::cout<<std::endl;

    }

    const std::set<std::vector<Vertex>>& getAllPaths() const {
           return all_paths_set_;
       }
};



typedef boost::graph_traits<BoostAdjacencyMatrix>::edge_descriptor Edge;

void hybrid_automata::bglDFSpaths(BoostAdjacencyMatrix adjacencyMatrix, Vertex start, Vertex end, int max_depth) {
    //AllPathsVisitor visitor(end);

     //Create a color map to store the vertex colors during DFS
    //std::vector<boost::default_color_type> color_map(boost::num_vertices(adjacencyMatrix));

    std::vector<boost::default_color_type> color_map(boost::num_vertices(adjacencyMatrix), boost::white_color);
    //AllPathsVisitor visitor(end, &color_map[0]);
    AllPathsVisitor visitor(start, end, &color_map[0], max_depth);
        boost::depth_first_search(adjacencyMatrix, boost::visitor(visitor).root_vertex(start).color_map(&color_map[0]));
}

