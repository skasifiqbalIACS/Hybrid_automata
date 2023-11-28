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

math::matrix<transition::ptr> hybrid_automata::getGraph() {
    int numLocations = getTotalLocations();
    std::cout << "Number of Locations: " << numLocations << std::endl;

    // Initialize an adjacency matrix with all null pointers
    math::matrix<transition::ptr> adjacencyMatrix(numLocations, numLocations, nullptr);

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
                // Populate the adjacency matrix with the transition pointer
                adjacencyMatrix(adjustedSourceId, adjustedDestId) = transitionPtr;
            }
            else {
                std::cerr << "Invalid location IDs: " << sourceLocationId << ", " << destinationLocationId << std::endl;
            }
        }
    }
    return adjacencyMatrix;
}

// Define a new graph type that uses an adjacency_list and associates
// each edge with a transition::ptr
// Define the Boost Graph using edge properties
typedef boost::property<boost::edge_name_t, transition::ptr> EdgeProperty;
typedef boost::adjacency_matrix<boost::directedS, int, EdgeProperty> BoostAdjacencyMatrixWithTransitions;

BoostAdjacencyMatrixWithTransitions hybrid_automata::bglGraph(math::matrix<transition::ptr>) {
    int numLocations = getTotalLocations();
    BoostAdjacencyMatrixWithTransitions graph(numLocations);

    std::map<int, location::ptr> allLocations = getAllLocations();
    for (const std::pair<int, location::ptr>& locationPair : allLocations) {
        int sourceLocationId = locationPair.first;

        // Get the list of outgoing transitions from the source location
        std::list<transition::ptr> outgoingTransitions = locationPair.second->getOutGoingTransitions();

        // Iterate through the outgoing transitions
        for (const transition::ptr& transitionPtr : outgoingTransitions) {
            int destinationLocationId = transitionPtr->getDestinationLocationId();
            boost::add_edge(sourceLocationId - 1, destinationLocationId - 1, transitionPtr, graph);
        }
    }

    return graph;
}

typedef boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::vertex_descriptor Vertex;

void hybrid_automata::printGraph(const BoostAdjacencyMatrixWithTransitions& graph) {
    using Vertex = boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::vertex_descriptor;
    using OutEdgeIterator = boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::out_edge_iterator;

    for (Vertex u = 0; u < num_vertices(graph); ++u) {
        std::cout << "Location " << (u + 1) << "-> "; // Adjusting for 1-based location indexing

        std::pair<OutEdgeIterator, OutEdgeIterator> outEdges = out_edges(u, graph);
        for (OutEdgeIterator ei = outEdges.first; ei != outEdges.second; ++ei) {
            Vertex v = target(*ei, graph);
            transition::ptr trans = boost::get(boost::edge_name, graph, *ei);
            std::cout << "- (" << trans->getTransitionId() << ") " << "- " << (v + 1) ; // Adjusting for 1-based location indexing
        }

        std::cout << std::endl;
    }
}

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
    std::vector<transition::ptr> current_transitions_;
    std::map<Vertex, int> current_path_count_; // Store visit counts for each vertex

public:
    std::set<std::pair<std::vector<Vertex>, std::vector<transition::ptr>>> all_paths_set_; // Store unique paths
//    std::set<std::vector<Vertex>> all_paths_set_; // Store unique paths
    Vertex start_vertex_;
    Vertex destination_vertex_;
    boost::default_color_type* color_map_; // Color map to manage the visited status of the vertices
    int max_depth_;
    int path_no_ = 0;

    hybrid_automata* haInstance;
    AllPathsVisitor(hybrid_automata* instance, Vertex start, Vertex destination, boost::default_color_type* color_map, int max_depth)
        : haInstance(instance), start_vertex_(start), destination_vertex_(destination), color_map_(color_map), max_depth_(max_depth) {}

    void discover_vertex(Vertex u, const BoostAdjacencyMatrixWithTransitions& g) {
        if (!current_path_.empty()) {
            if (!boost::edge(current_path_.back(), u, g).second) {
                return;
            }
        } else if (u != start_vertex_) {
            return;
        }
        current_path_.push_back(u);
        current_path_count_[u]++;
        if (current_path_.size() > max_depth_) return;
        put(color_map_, u, boost::white_color);
    }

    void tree_edge(const boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::edge_descriptor& e, const BoostAdjacencyMatrixWithTransitions& g) {
        Vertex u = source(e, g);
    	Vertex v = target(e, g);
        transition::ptr t = boost::get(boost::edge_name, g, e);

        if (!current_path_.empty() && current_path_.back() == u) {
		   // The transition 't' is valid for insertion into current_transitions_.
		   current_transitions_.push_back(t);
	   }

        if (v == destination_vertex_ && current_path_.size() + 1 <= max_depth_) {
            bool inserted;
//            current_transitions_.push_back(t);
            tie(std::ignore, inserted) = all_paths_set_.insert({current_path_, current_transitions_});
//            tie(std::ignore, inserted) = all_paths_set_.insert({current_path_});
            if (inserted) {
                path_no_++;
                std::cout << "Unique Path: " << path_no_ << " ";

                std::vector<location::const_ptr> current_location_path;

                for (size_t i = 0; i < current_path_.size(); i++) {
                    location::const_ptr loc = haInstance->getLocation(current_path_[i] + 1);  // Fetch the location pointer for each location ID.
                    current_location_path.push_back(loc);  // Store the location in the current location path
                    std::cout << loc->getName();

                    if (i < current_transitions_.size()) {
                        std::cout << " - (" << current_transitions_[i]->getTransitionId() << ") -> ";
                    }
                }

                // Directly print the destination vertex (location) after the path.
                location::const_ptr destinationLoc = haInstance->getLocation(v + 1);
                current_location_path.push_back(destinationLoc);  // Store the destination location in the current location path
                std::cout << destinationLoc->getName() << std::endl;
//                std::cout << "length of the path" <<  current_location_path.size() << std::endl;
                if(current_location_path.size() > 1){
                	haInstance->generateXmlAndCfgFromPath(current_location_path, current_transitions_, path_no_);
                }
            }
        }
    }

    void back_edge(const boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::edge_descriptor& e, const BoostAdjacencyMatrixWithTransitions& g) {
        Vertex u = source(e, g);
        Vertex v = target(e, g);
        if (!boost::edge(u, v, g).second) return;
        //put(color_map_, v, boost::white_color);
    }

    void finish_vertex(Vertex u, const BoostAdjacencyMatrixWithTransitions& g) {
        if (current_path_count_[u] > 0) {
            put(color_map_, u, boost::white_color);
            current_path_count_[u]--;
        }
        if (!current_path_.empty()) {
            current_path_.pop_back();
        }
        if (!current_transitions_.empty()) {
            current_transitions_.pop_back();
        }
    }
};

    /*void examine_edge(const boost::graph_traits<BoostAdjacencyMatrix>::edge_descriptor& e, const BoostAdjacencyMatrix& g) {
        Vertex u = source(e, g);
        Vertex v = target(e, g);
//        std::cout << "Examining edge: " << u << " -> " << v << std::endl;
//        std::cout << "Vertex " << u << " color: " << getColorName(color_map_[u]) << std::endl;
//        std::cout << "Vertex " << v << " color: " << getColorName(color_map_[v]) << std::endl;

    }*/

typedef boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::edge_descriptor Edge;

void hybrid_automata::bglDFSpaths(BoostAdjacencyMatrixWithTransitions adjacencyMatrix, Vertex start, Vertex end, int max_depth) {
    std::vector<boost::default_color_type> color_map(boost::num_vertices(adjacencyMatrix), boost::white_color);
    AllPathsVisitor visitor(this, start, end, &color_map[0], max_depth);
    boost::depth_first_search(adjacencyMatrix, boost::visitor(visitor).root_vertex(start).color_map(&color_map[0]));
    printUnsatPathResponsibleEdges();
}


#include <boost/make_shared.hpp>


/*void hybrid_automata::findAllPathsDFS(Vertex current, Vertex destination, std::vector<boost::shared_ptr<location>>& path,
                         std::vector<boost::shared_ptr<transition>>& transitions, std::set<std::pair<std::vector<boost::shared_ptr<location>>, std::vector<boost::shared_ptr<transition>>>>& all_paths,
                         math::matrix<boost::shared_ptr<transition>>& adjacencyMatrix, int max_depth, int& path_no){

	if (path.size() > max_depth) return; // Check if the current path exceeds maximum depth

	path.push_back(getLocation(current + 1)); // Convert zero-based index to one-based ID and push location pointer

	if (current == destination) {
		if (path.size() <= max_depth) {
			all_paths.insert({path, transitions}); // Insert the current path and transitions into the set of all paths
			path_no++;
//			generateXmlAndCfgFromPath(path, transitions, path_no); // Generate XML and CFG
		}
	} else {
		for (Vertex next = 0; next < adjacencyMatrix.size1(); ++next) { // Iterate through possible next vertices
			if (adjacencyMatrix(current, next)) { // Check if there is a transition to the next vertex
			   transitions.push_back(adjacencyMatrix(current, next)); // Push the transition pointer
			   findAllPathsDFS(next, destination, path, transitions, all_paths, adjacencyMatrix, max_depth, path_no);
			   transitions.pop_back(); // Backtrack: remove the last transition
			}
		}
	}

	path.pop_back(); // Backtrack: remove the last location from the path
}

// A method to initiate the search and process the results
void hybrid_automata::customDFSPaths(Vertex start, Vertex destination, int max_depth) {
	math::matrix<transition::ptr> adjacencyMatrix = getGraph(); // Get the graph's adjacency matrix
	std::set<std::pair<std::vector<location::ptr>, std::vector<transition::ptr>>> all_paths;
	int path_no = 0;
	std::vector<location::ptr> path;
	std::vector<transition::ptr> transitions;

	findAllPathsDFS(start, destination, path, transitions, all_paths, adjacencyMatrix, max_depth, path_no);

	// Print all unique paths and their transitions
	for (const auto& path_transitions_pair : all_paths) {
	const auto& loc_path = path_transitions_pair.first;
	const auto& trans_path = path_transitions_pair.second;
	std::cout << "Path " << path_no << ": ";
	for (size_t i = 0; i < loc_path.size(); ++i) {
	std::cout << loc_path[i]->getName();
	if (i < trans_path.size()) {
	   std::cout << " -[trans:" << trans_path[i]->getTransitionId() << "]-> ";
	}
	}
	std::cout << std::endl;
	}
}*/


structuralPath::ptr hybrid_automata::createStructuralPath(
    const std::vector<location::const_ptr>& currentPathLocations,
    const std::vector<transition::ptr>& currentPathTransitions)
{
    if (currentPathLocations.empty() || currentPathTransitions.empty()) {
        std::cerr << "Error: Empty locations or transitions provided." << std::endl;
        return nullptr;  // return null pointer if error
    }

    // Convert the vectors to std::list
    std::list<location::const_ptr> path_locations(currentPathLocations.begin(), currentPathLocations.end());
    std::list<transition::ptr> path_transitions(currentPathTransitions.begin(), currentPathTransitions.end());

    // Create a structuralPath object from these lists
    structuralPath::ptr ptr = boost::make_shared<structuralPath>(path_locations, path_transitions);

    return ptr;
}

void hybrid_automata::generateXmlAndCfgFromPath(
    const std::vector<location::const_ptr>& currentPathLocations,
    const std::vector<transition::ptr>& currentPathTransitions,
    int& pathNo)
{

	static std::unordered_set<string> feasiblePaths;
	static std::unordered_set<string> infeasiblePaths;


    // Create the structural path first
    structuralPath::ptr ptr = createStructuralPath(currentPathLocations, currentPathTransitions);

    // Creation status
    if (!ptr) {
        std::cerr << "Failed to create structural path." << std::endl;
        return;
    }

    // Generate the xml & cfg for a linear path automata from human model
    string str;
    bool path_feasible;
    if (true) {  // if (edge == nullptr) {
        //paths_replayed_in_agent_model++;

        fstream file, file1;
        string file_path = "/home/asif/eclipse-workspace/XSpeed-plan/testcases/My_nav/unreachable/";
//        string model = "water_level_monitor_human";
//        string model = "water_level_monitor_agent";
        string model = "warehouse_automation_agent1";
//        string model = "warehouse_automation_human1";

        string xml_file = file_path + model + ".xml";
        string cfg_file = file_path + model + ".cfg";
        file.open(xml_file, ios::out | ios::in);
        std::cout << "Opening " << xml_file << endl;

        // generates the xml file for a linear path automata from human model
        if (file.is_open()) {
            str = this->generateXml(file, ptr, file_path, model, pathNo);
        }
        file.close();

        // generates the cfg file for a linear path automata from human model
        file1.open(cfg_file, ios::out | ios::in);
        std::cout << "Opening " << cfg_file << endl;
        bool agent_model = true;
        if (file1.is_open()) {
            this->generatecfg(file1, ptr, file_path, model, pathNo, agent_model);
        }
        file1.close();

        // Calling cH_Replay() (continuous replay) to check feasibility of a path in the human model
        path_feasible = this->cH_Replay(str);
        string path_str = str;

        if (path_feasible == false) {
//            infeasiblePaths.push_back(ptr);
        	// Iterate through the path, break it into components and check each by cH_Replay
			int j =1;
			bool pathInfeasible = false;  // Flag to check if current path is infeasible

        	for (size_t i = 2; i <= currentPathLocations.size(); ++i) {

				// Create a sub-path
				std::vector<location::const_ptr> subPathLocations(currentPathLocations.begin(), currentPathLocations.begin() + i);
				std::vector<transition::ptr> subPathTransitions(currentPathTransitions.begin(), currentPathTransitions.begin() + i - 1);

				string subPathKey = generateKey(subPathLocations);

				/*std::cout << "SubPathLocations: ";
				for(const auto& loc : subPathLocations) {
				    std::cout << loc->getName() << " ";
				}
				std::cout << std::endl;

				// Printing subPathTransitions
				std::cout << "SubPathTransitions: ";
				for(const auto& trans : subPathTransitions) {
				    std::cout << trans->getTransitionId() << " ";
				}
				std::cout << std::endl;*/

				/* for (const auto& pathKey : infeasiblePaths) {
				        std::cout << "Infeasible Path: " << pathKey << std::endl;
				 }*/
				// Generates the xml & cfg for this sub-path
				structuralPath::ptr subPathPtr = createStructuralPath(subPathLocations, subPathTransitions);
				if (!subPathPtr) {
					std::cerr << "Failed to create sub structural path." << std::endl;
					continue; // Move to next iteration
				}

				if (feasiblePaths.find(subPathKey) != feasiblePaths.end()) {
				    std::cout << "Subpath already explored" << endl;
					continue;
				}
				if (infeasiblePaths.find(subPathKey) != infeasiblePaths.end()) {
					std::cout << "Subpath ending at location " << subPathLocations.back()->getName() << " is known to be infeasible due to transition" << subPathTransitions.back()->getTransitionId() << std::endl;
					 pathInfeasible = true;  // Set the flag
	                 unsatPathResponsibleEdge[generateKey(currentPathLocations)] = subPathTransitions.back();

					 break;

//					continue;
				}

				/*fstream subFile, subFile1;
				string subXml_file = path_str + ".xml";
				string subCfg_file = path_str + ".cfg";
//				file_path = path_str;
				string sub_model = model + "_sub_" + to_string(j++);
				subFile.open(subXml_file, ios::out | ios::in);

				if (subFile.is_open()) {
					std::cout << subXml_file << " is open" <<std::endl;
					str = this->generateXml(subFile, subPathPtr, file_path, sub_model, pathNo);
				}
				subFile.close();

				subFile1.open(subCfg_file, ios::out | ios::in);
				if (subFile1.is_open()) {
					agent_model = true;
					this->generatecfg(subFile1, subPathPtr, file_path, sub_model, pathNo, agent_model);
				}
				subFile1.close();*/

				fstream subFile, subFile1;
				string subXml_file = file_path + model + ".xml";
				string subCfg_file = file_path + model + ".cfg";
//				file_path = file_path + "results/";
				string sub_model = model + "_sub_" + to_string(j++);
				subFile.open(subXml_file, ios::out | ios::in);

				if (subFile.is_open()) {
//					std::cout << subXml_file << " is open" <<std::endl;
					str = this->generateXml(subFile, subPathPtr, file_path, sub_model, pathNo);
				}
				subFile.close();

				subFile1.open(subCfg_file, ios::out | ios::in);
				if (subFile1.is_open()) {
					agent_model = true;
//					agent_model = true;
					this->generatecfg(subFile1, subPathPtr, file_path, sub_model, pathNo, agent_model);
				}
				subFile1.close();


				// Check feasibility of this sub-path
				bool subPathFeasible = this->cH_Replay(str);
				if (subPathFeasible) {
				    feasiblePaths.insert(subPathKey);
				} else {
					std::cout << "Subpath ending at location " << subPathLocations.back()->getName() << " is infeasible due to transition" << subPathTransitions.back()->getTransitionId() << std::endl;
				    infeasiblePaths.insert(subPathKey);
//				    unsatPathResponsibleEdge[generateKey(currentPathLocations)] = subPathTransitions.back();
				    unsatPathResponsibleEdge[generateKey(currentPathLocations)] = subPathTransitions.back();
				    break;
				}


//				auto result = this->cA_Replay(str);

			}

        	/*if (pathInfeasible) {
        	    std::cout << "The entire path is infeasible due to a known infeasible subpath." << std::endl;
        	    continue;
        	}*/

        }
	else {
			// For a feasible path, we simply record a nullptr for the whole path
			string fullPathKey = generateKey(currentPathLocations);
			unsatPathResponsibleEdge[fullPathKey] = nullptr;
		}
    }
}

/*
void hybrid_automata::generateXmlAndCfgFromPath(
    const std::vector<location::const_ptr>& currentPathLocations,
    const std::vector<transition::ptr>& currentPathTransitions,
    int& pathNo)
{
    // Create the structural path
    structuralPath::ptr ptr = createStructuralPath(currentPathLocations, currentPathTransitions);

    if (!ptr) {
        std::cerr << "Failed to create structural path." << std::endl;
        return;
    }

    fstream file, file1;
    string file_path = "/home/asif/eclipse-workspace/XSpeed-plan/testcases/My_nav/unreachable/";
    string model = "water_level_monitor_agent";

    bool path_feasible = this->cH_Replay(this->generateXml(file, ptr, file_path, model, pathNo));

    if (path_feasible == false) {
        // Handle the infeasible main path here if necessary

        // Split the path into sub-paths and generate XML & CFG for each sub-path
        for (size_t i = 2; i <= currentPathLocations.size(); ++i) {

            // Create a sub-path
            std::vector<location::const_ptr> subPathLocations(currentPathLocations.begin(), currentPathLocations.begin() + i);
            std::vector<transition::ptr> subPathTransitions(currentPathTransitions.begin(), currentPathTransitions.begin() + i - 1);

            // Create the structural path for this sub-path
            structuralPath::ptr subPathPtr = createStructuralPath(subPathLocations, subPathTransitions);
            if (!subPathPtr) {
                std::cerr << "Failed to create sub structural path." << std::endl;
                continue; // Move to next iteration
            }

            string sub_model = model + "_sub_" + to_string(i-1);

            // Generate the XML file for this sub-path
            string xmlFileName = file_path + "results/" + sub_model + "_path" + to_string(pathNo) + ".xml";
            file.open(xmlFileName, ios::out);
            if (file.is_open()) {
                this->generateXml(file, subPathPtr, file_path, sub_model, pathNo);
            }
            file.close();

            // Generate the CFG file for this sub-path
            string cfgFileName = file_path + "results/" + sub_model + "_path" + to_string(pathNo) + ".cfg";
            file1.open(cfgFileName, ios::out);
            if (file1.is_open()) {
                this->generatecfg(file1, subPathPtr, file_path, sub_model, pathNo, true);
            }
            file1.close();

            // Check feasibility of this sub-path
            bool subPathFeasible = this->cH_Replay(xmlFileName);

            if (!subPathFeasible) {
                std::cout << "Subpath ending at vertex " << i << " is infeasible." << std::endl;
            }
        }
    }
}
*/

string hybrid_automata::generateKey(const std::vector<location::const_ptr>& subPathLocations) {
    string key = "";
    for (const auto& loc : subPathLocations) {
        key += loc->getName() + ";"; // assuming ';' doesn't appear in names
    }
    return key;
}

void hybrid_automata::printUnsatPathResponsibleEdges() {

        for (const auto& path_edge_pair : unsatPathResponsibleEdge) {
            // Print out the path
            std::cout << "Path: ";
            for (auto vertex : path_edge_pair.first) {
                std::cout << vertex ; // replace int with the appropriate type for Vertex if needed
            }

            // Print out the corresponding transition's ID or nullptr if it doesn't exist
            if (path_edge_pair.second) {
                std::cout << " - Unsat Edge: " << path_edge_pair.second->getTransitionId();
            } else {
                std::cout << " - No responsible unsatisfactory edge";
            }

            std::cout << std::endl;
        }
    }

void hybrid_automata::generatecfg(fstream& file1, structuralPath::ptr path, string file_path, string model, int pathNo, bool agent_model){
	string line;
	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;

	string str = file_path + "results/" + model + "_path" + to_string(pathNo); //path of generated cfg file
	string str_cfg = str + ".cfg"; //output cfg file

	fstream fileout;
	fileout.open(str_cfg, ios::out);

	std::list<location::const_ptr> path_locations = path->get_path_locations(); //list of locations
	std::list<location::const_ptr>::iterator locIter1 = path_locations.begin();
	int strt_loc = (*locIter1)->getLocId();
	std::advance(locIter1, (path_locations.size() - 1));
	int end_loc = (*locIter1)->getLocId();

	while (getline(file1, line)){

		if(line.compare("")==0)			// if empty line, then continue
			continue;

		boost::char_separator<char> sep(" <>=:\"");
		tokenizer tokens(line,sep);
		tokenizer::iterator tok_iter;

		for(tok_iter = tokens.begin(); tok_iter != tokens.end(); ++tok_iter){

			//std::cout<<"<"<<*tok_iter<<"> ";
		    if (*tok_iter == "initially"){
		    	if (agent_model){
		    		//warehouse automation agent:
		    		  //prob01:
//		    		    fileout<<"initially = \"x1==0.5 & x2==1.5 & c==1 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		    fileout<<"initially = \"x1==0.5 & x2==1.5 & c==4 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		  //prob02
		    		    //fileout<<"initially = \"x1==0.5 & x2==3.5 & c==5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		  //prob03
		    		    //fileout<<"initially = \"x1==0.5 & x2==3.5 & c==5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		//water level monitor agent:
//		    		fileout<<"initially = \"x1==0 & x2==0 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    	}
		    	else {
		    		//warehouse automation human:
		    		  //prob01:
//		    		    fileout<<"initially = \"x1==0.5 & x2==1.5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		    fileout<<"initially = \"x1==0.5 & x2==1.5 & c==5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		  //prob02:
		    		    //fileout<<"initially = \"x1==0.5 & x2==3.5 & c==5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		  //prob03
		    		    //fileout<<"initially = \"x1==0.5 & x2==3.5 & c==5 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    		//water level monitor human:
//		    		fileout<<"initially = \"x1==0 & x2==0 & loc()==loc"<<strt_loc<<"001\""<<endl;
		    	}
		    	break;
		    }
		    else if (*tok_iter == "forbidden"){
		    	fileout<<"forbidden = \"loc()==loc"<<end_loc<<"00"<<path_locations.size()<<"\""<<endl;
		    	break;
		    }
		    else {
		    	fileout<<line<<endl;
		    	break;
		    }
		}
		//std::cout<<""<<endl;
	}

	/****** Writing cfg file ******/
	//fstream filein_cfg, fileout_cfg;
/*	fstream fileout_cfg;
	//string cfg_path = file_path + ".cfg";
	//filein_cfg.open(cfg_path, ios::in);
	string str_cfg = str + ".cfg"; //output cfg file
	fileout_cfg.open(str_cfg, ios::out); */

	/*if (filein_cfg.open){
		// if empty line, then continue
		if(line.compare("")==0)
			continue;
		else
			fileout_cfg<<line<<endl;
	} */

/*	fileout_cfg<<"# analysis options"<<endl;
	fileout_cfg<<"system = \"nav_model_human\""<<endl;
	std::list<location::const_ptr>::iterator locIter1 = path_locations.begin();
	int strt_loc = (*locIter1)->getLocId();
	//fileout_cfg<<"initially = \"x1==0.5 & x2==1.5 & z>=-1 & z<=1 & loc()==loc"<<strt_loc<<"001\""<<endl;
	fileout_cfg<<"initially = \"x1==0.5 & x2==1.5 & loc()==loc"<<strt_loc<<"001\""<<endl;
	//int path_size = path_locations.size() - 1;
	std::advance(locIter1, (path_locations.size() - 1));
	//locIter1 = path_locations.end();
	int end_loc = (*locIter1)->getLocId();
	fileout_cfg<<"forbidden=\"loc()==loc"<<end_loc<<"00"<<path_locations.size()<<"\""<<endl;
	fileout_cfg<<"iter-max = 50"<<endl;
	fileout_cfg<<"rel-err = 1.0e-12"<<endl;
	fileout_cfg<<"abs-err = 1.0e-13"<<endl; */
	/************************/
	fileout.close();
}

string hybrid_automata::generateXml(fstream& file, structuralPath::ptr path, string file_path, string model, int pathNo){
	//fstream file;
	string line;
	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
	//typedef boost::tokenizer<boost::escaped_list_separator<char> > tokenizer;

	//std::cout<<"opening nav_model_human_2.xml"<<endl;
	//file.open("/home/iacs1/eclipse-workspace/XSpeed/testcases/My_nav/unreachable/nav_model_human_2.xml", ios::out | ios::in);
	//file.open("nav_model_human_2.xml", ios::out | ios::in);

	//string str = "/home/iacs1/eclipse-workspace/XSpeed/testcases/My_nav/unreachable/nav_model_human_path" + to_string(pathNo); //path of xml & cfg file
	string str = file_path + "results/" + model + "_path" + to_string(pathNo); //path of generated xml & cfg file
	string str_xml = str + ".xml"; //output xml file

	//std::array<std::string,2> fileXmlCfg{str, str_cfg};	//for returning xml and cfg file
	fstream fileout;
	//fileout.open("/home/iacs1/eclipse-workspace/XSpeed/testcases/My_nav/unreachable/nav_model_human_2_path.txt", ios::out);
	fileout.open(str_xml, ios::out);

	//std::vector<std::string> loc_inv;	//storing location invariant
	//std::vector<std::string> loc_flow;	//storing location flow
	std::array<std::string,100> loc_inv;	//storing location invariant
	std::array<std::string,100> loc_flow;	//storing location flow
	std::array<std::string,100> trans_guard;	//storing transition guard
	std::array<std::string,100>trans_assignment; //storing transition assignment

	//if (file.is_open()) {
		while (getline(file, line)){
			// if empty line, then continue
			if(line.compare("")==0){
				continue;
			}

			//char_separator<char> sep(" <>=:");
			boost::char_separator<char> sep(" <>=:\"");
			//boost::escaped_list_separator<char> sep( ' ', '\"', '\=' );
			//tokenizer<char_separator<char> > tokens(line,sep);
			//boost::tokenizer<char_separator<char> > tokens(line,sep);
			tokenizer tokens(line,sep);
			//tokenizer<escaped_list_separator<char> > tokens (line, sep);
			//boost::tokenizer<char_separator<char> >::iterator tok_iter;
			tokenizer::iterator tok_iter;
			int tokNo = 0;
			for(tok_iter = tokens.begin(); tok_iter != tokens.end(); ++tok_iter){
				tokNo++;
			    //std::cout << "<" << *tok_iter << "> ";
			    //fileout<<"<" << *tok_iter << "> ";
			    if(*tok_iter == "?xml" || *tok_iter == "sspaceex" || *tok_iter == "version"
			    	|| *tok_iter == "component"){
			    	fileout<<line<<endl;
			    	break;
			    }

			    else if (*tok_iter == "param"){
					//tok_iter = tok_iter + 2;
			    	std::advance(tok_iter, 2);
					regex strExpr("(e)(.*)");
					if (!regex_match(*tok_iter, strExpr)){
						fileout<<line<<endl;
						break;
					}
					else {
//						fileout<<line<<endl;
						break;
					}
				}

			    else if(*tok_iter == "location" ){
			    	std::advance(tok_iter, 2);
			    	int locID = stoi(*tok_iter);
			    	//tok_iter = tok_iter + 2;
			    	getline(file, line); //line++;
			    	//std::cout<<line<<endl;
					boost::char_separator<char> sep3(" <>=:\"");
			    	tokenizer tokens3(line, sep3);
					tokenizer::iterator tok_iter3 = tokens3.begin();
					if (*tok_iter3 == "invariant"){
						//loc_inv.push_back(line);
						loc_inv[locID] = line;
				    	getline(file, line); //line++;
				    	//loc_flow.push_back(line);
				    	loc_flow[locID] = line;
				    	break;
					}
					else {
				    	//loc_flow.push_back(line);
						loc_flow[locID] = line;
				    	break;
					}


			    }
			    else if(*tok_iter == "transition"){
			    	getline(file, line); //line++;
					boost::char_separator<char> sep1(" <>=:\"e");
			    	tokenizer tokens1(line, sep1);
					tokenizer::iterator tok_iter1;
					for(tok_iter1 = tokens1.begin(); tok_iter1 != tokens1.end(); ++tok_iter1){
						if (*tok_iter1 == "lab"){
							//tok_iter1 = tok_iter1 + 2;
							std::advance(tok_iter1, 2);
							int edgeId = stoi(*tok_iter1);
							getline(file, line); //line++;
							boost::char_separator<char> sep2(" <>=:\"");
					    	tokenizer tokens2(line, sep2);
							tokenizer::iterator tok_iter2 = tokens2.begin();
							if(*tok_iter2 == "guard"){
								trans_guard[edgeId] = line;
								getline(file, line);
								boost::char_separator<char> sep4(" <>=:\"");
						    	tokenizer tokens4(line, sep4);
								tokenizer::iterator tok_iter4 = tokens4.begin();
								if (*tok_iter4 == "assignment"){
									trans_assignment[edgeId] = line;
								}
								break;
							}
							else if (*tok_iter2 == "assignment"){
								trans_assignment[edgeId] = line;
								break;
							}


						}
					}
					break;
			    }
			    else {
			    	break;
			    }

			}
			//std::cout<<" Number of tokens: "<<tokNo;
			//fileout<<" Number of tokens: "<<tokNo;
			//std::cout << "\n";
			//fileout<< "\n";
		}

	//}
	//file.close();

	/* setting transitions in the xml */
	std::list<transition::ptr> path_transitions = path->get_path_transitions(); //list of transitions
	int transNo = 0;	//number of transitions in the path
	for (auto it = path_transitions.begin(); it != path_transitions.end(); it++){
		transNo++;
		int transId = (*it)->getTransitionId();
		string str1 = "e" + to_string(transId) + "00" + to_string(transNo);
		fileout<<"    <param name=\""<<str1<<"\" type=\"label\" local=\"false\" />"<<endl;
	}

	/* setting locations in the xml */
	std::list<location::const_ptr> path_locations = path->get_path_locations(); //list of locations
	int locsNo = 0;		//number of locations in the path
	for(auto it = path_locations.begin(); it !=path_locations.end(); it++){
		locsNo++;
		int locId = (*it)->getLocId();
		string str2 = to_string(locId) + "00" + to_string(locsNo);
		fileout<<"    <location id=\""<<str2<<"\" name=\"loc"<<str2<<"\">"<<endl;
		fileout<<loc_inv[locId]<<endl;
		fileout<<loc_flow[locId]<<endl;
		fileout<<"    </location>"<<endl;
	}

	/* setting transitions in the xml */
	//std::list<transition::ptr> path_transitions = path->get_path_transitions(); //list of transitions
	transNo = 0;	//number of transitions in the path
	locsNo = 1;		//number of locations in the path
	std::list<location::const_ptr>::iterator locIter = path_locations.begin();
	for (auto it = path_transitions.begin(); it != path_transitions.end(); it++){
		transNo++;
		int transId = (*it)->getTransitionId();
		string str1 = "e" + to_string(transId) + "00" + to_string(transNo);
		int source = (*locIter)->getLocId();
		string str2 = to_string(source) + "00" + to_string(locsNo);
		std::advance(locIter, 1);
		int target = (*locIter)->getLocId();
		locsNo++;
		string str3 = to_string(target) + "00" + to_string(locsNo);
		fileout<<"    <transition source=\""<<str2<<"\" target=\""<<str3<<"\">"<<endl;
		fileout<<"      <label>"<<str1<<"</label>"<<endl;
		fileout<<trans_guard[transId]<<endl;
		fileout<<trans_assignment[transId]<<endl;
		fileout<<"    </transition>"<<endl;
	}

	fileout<<"  </component>"<<endl;
	fileout<<"</sspaceex>"<<endl;

	fileout.close();

	return str; //returning path to xml & cfg file
}

bool hybrid_automata::cH_Replay(const string& str) {
    // The string cmd_str for invoking a system command
    string cmd_str = "runlim -s 4096 -t 1000 -r 1000 -o " + str + ".runlim"
            + " " + "/home/asif/BACH-5.5/bach -t -p -v2 -solver cmsat -semantics mixed" + " " +
            str + ".xml" + " " + str + ".cfg"
            + " 20 >" + " " + str + "BACH.log";
    system(cmd_str.c_str()); // calling BACH

    bool path_feasible = false;	// returns feasibility of a path

    fstream file;
    string line;
    typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
    file.open(str + "BACH.log", ios::out | ios::in);
    std::cout << "opening " + str + "BACH.log" << endl;
    if (file.is_open()) {
        while (getline(file, line)) {
            if (line.compare("") == 0) {
                continue;
            }

            boost::char_separator<char> sep(" $()[]-><=\t\"");
            tokenizer tokens(line, sep);
            tokenizer::iterator tok_iter = tokens.begin();

            if (*tok_iter == "sat") {
                path_feasible = true;
                break;
            }
            else {
                continue;
            }
        }
    }
    file.close();
    return path_feasible;
}

std::pair<vector<int>, vector<int> > hybrid_automata::cA_Replay(string str){
/*	string cmd_str = "runlim -s 4096 -t 1000 -r 1000 -o " + str + ".runlim"
			+ " " + "/home/iacs1/vmcai22BACH/bach -t -p -v2 -solver cmsat -semantics mixed" + " " +
			str + ".xml" + " " + str + ".cfg"
			+ " 10 >" + " " + str + "BACH.log"; */
	string cmd_str = "runlim -s 4096 -t 1000 -r 1000 -o " + str + ".runlim"
			+ " " + "/home/asif/BACH-5.5/bach -t -p -v2 -solver cmsat -semantics mixed" + " " +
			str + ".xml" + " " + str + ".cfg"
			+ " 20 >" + " " + str + "BACH.log";
	system(cmd_str.c_str()); //calling BACH

	vector<int> locs;	//store loc_ids of an IIS path segment
	vector<int> trans;	//store trans_ids of an IIS path segment
	std::pair<vector<int>, vector<int> > IIS_path_segment;

	//bool path_feasible = false;	//returns feasibility of a path

	fstream file;
	string line;
	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
	file.open(str + "BACH.log", ios::out | ios::in);
	std::cout<<"opening " + str + "BACH.log"<<endl;
	if (file.is_open()){
		while (getline(file, line)){
			// if empty line, then continue
			if(line.compare("")==0)
				continue;

			boost::char_separator<char> sep(" $()[]-><=\t\"");
			tokenizer tokens(line,sep);
			tokenizer::iterator tok_iter;
			//int tokNo = 0;
			tok_iter = tokens.begin();
			if (*tok_iter == "IIS"){
				//std::cout<<"Test"<<endl;
				//std::cout << "<" << *tok_iter << "> ";
				getline(file, line);
				boost::char_separator<char> sep1(" $()[]-><=\t\"");
		    	tokenizer tokens1(line, sep1);
				tokenizer::iterator tok_iter1;
				tok_iter1 = tokens1.begin();
				while (tok_iter1 != tokens1.end()){
					//tokNo++;
					//std::cout << "<" << *tok_iter1 << "> ";
					regex strExpr("(loc)(.*)");
					regex strExpr1("(e)(.*)");
					if (regex_match(*tok_iter1, strExpr)){
						string loc_name = *tok_iter1;
						string loc_id_str = "";
						char* char_array = new char[loc_name.length() + 1];
						strcpy(char_array, loc_name.c_str());
						//std::cout<<"loc id :"<<char_array[3]<<endl;
						if (char_array[3] != '0'){
							if (char_array[4] != '0'){
								if (char_array[5] != '0'){
									loc_id_str = loc_id_str + char_array[3] + char_array[4] + char_array[5];
								}
								else loc_id_str = loc_id_str + char_array[3] + char_array[4];
							}
							else loc_id_str = loc_id_str + char_array[3];
						}
						//std::cout<<loc_id_str<<endl;
						delete[] char_array;
						int loc_id = stoi(loc_id_str);
						//std::cout<<"IIS loc id: "<<loc_id<<endl;
						//location::const_ptr locPtr = haPtrx->getLocation(loc_id);
						locs.push_back(loc_id);
						//std:cout<<"Loc Id: "<<loc_id<<endl;
					}
					else if (regex_match(*tok_iter1, strExpr1)){
						string trans_name = *tok_iter1;
						string trans_id_str = "";
						char* char_array1 = new char[trans_name.length()+1];
						strcpy(char_array1, trans_name.c_str());
						if (char_array1[1] != '0'){
							if (char_array1[2] != '0'){
								if (char_array1[3] != '0'){
									trans_id_str = trans_id_str + char_array1[1] + char_array1[2] + char_array1[3];
								}
								else trans_id_str = trans_id_str + char_array1[1] + char_array1[2];
							}
							else trans_id_str = trans_id_str + char_array1[1];
						}
						//std::cout<<trans_id_str<<endl;
						delete[] char_array1;
						int trans_id = stoi(trans_id_str);
						//std::cout<<"IIS trans id: "<<trans_id<<endl;
						trans.push_back(trans_id);
						//std::cout<<"Trans Id: "<<trans_id<<endl;
					}
					std::advance(tok_iter1,1);
				}
				//std::cout<<" Number of tokens: "<<tokNo;
				//std::cout<<"\n";
				IIS_path_segment.first = locs;
				IIS_path_segment.second = trans;
				break;
			}
			else continue;
		}
	}
	file.close();
	std::cout<<"IIS locs are: ";
	for (unsigned int i = 0; i < IIS_path_segment.first.size(); i++) {
		std::cout<<IIS_path_segment.first[i]<<" ";
	}
	std::cout<<"\n";
	std::cout<<"IIS trans are: ";
	for (unsigned int i = 0; i < IIS_path_segment.second.size(); i++) {
		std::cout<<IIS_path_segment.second[i]<<" ";
	}
	std::cout<<"\n";
	return IIS_path_segment;

}
