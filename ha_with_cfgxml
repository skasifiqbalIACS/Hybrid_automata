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




void hybrid_automata::printGraph(math::matrix<transition::ptr>& mat) {
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
        if (current_path_.size() >= max_depth_) return;
        put(color_map_, u, boost::white_color);
    }

    void tree_edge(const boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::edge_descriptor& e, const BoostAdjacencyMatrixWithTransitions& g) {
        Vertex v = target(e, g);
        transition::ptr t = boost::get(boost::edge_name, g, e);
        current_transitions_.push_back(t);

        if (v == destination_vertex_ && current_path_.size() + 1 <= max_depth_) {
            bool inserted;
            tie(std::ignore, inserted) = all_paths_set_.insert({current_path_, current_transitions_});
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

    const std::set<std::pair<std::vector<Vertex>, std::vector<transition::ptr>>>& getAllPaths() const {
        return all_paths_set_;
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
}



void generatecfg(fstream& file1,
				const std::vector<location::const_ptr>& current_location_paths,
				const std::vector<transition::ptr>& current_transition_paths,
				string file_path, string model, int pathNo, bool agent_model) {
    string line;
    typedef boost::tokenizer<boost::char_separator<char>> tokenizer;

    string str = file_path + "results/" + model + "_path" + to_string(pathNo); // path of generated cfg file
    string str_cfg = str + ".cfg"; // output cfg file

    fstream fileout;
    fileout.open(str_cfg, ios::out);

    location::const_ptr start_loc_ptr = current_location_paths.front();
    location::const_ptr end_loc_ptr = current_location_paths.back();

    int strt_loc = start_loc_ptr->getLocId();
    int end_loc = end_loc_ptr->getLocId();

    while (getline(file1, line)) {

        if(line.compare("") == 0) // if empty line, then continue
            continue;

        boost::char_separator<char> sep(" <>=:\"");
        tokenizer tokens(line, sep);
        tokenizer::iterator tok_iter;

        for (tok_iter = tokens.begin(); tok_iter != tokens.end(); ++tok_iter) {

            if (*tok_iter == "initially") {
                // You can modify this part to reflect the initial conditions based on current_location_paths and current_transition_paths
                fileout << "initially = \"loc()==loc" << strt_loc << "001\""; // Example line; adjust as necessary
                fileout << endl;
                break;
            }
            else if (*tok_iter == "forbidden") {
                fileout << "forbidden = \"loc()==loc" << end_loc << "00" << current_location_paths.size() << "\"";
                fileout << endl;
                break;
            }
            else {
                fileout << line << endl;
                break;
            }
        }
    }

    fileout.close();
}

string replayPath::generateXml(fstream& file, const std::vector<location::const_ptr>& current_location_paths, const std::vector<transition::ptr>& current_transition_paths, string file_path, string model, int pathNo) {
    string line;
    typedef boost::tokenizer<boost::char_separator<char>> tokenizer;

    string str = file_path + "results/" + model + "_path" + to_string(pathNo); // path of generated xml file
    string str_xml = str + ".xml"; // output xml file

    fstream fileout;
    fileout.open(str_xml, ios::out);

    location::const_ptr start_loc_ptr = current_location_paths.front();
    location::const_ptr end_loc_ptr = current_location_paths.back();

    int strt_loc = start_loc_ptr->getLocId();
    int end_loc = end_loc_ptr->getLocId();

    while (getline(file, line)) {
        // ... [same code as before for processing the file lines]
    }

    /* Setting transitions in the xml */
    int transNo = 0;
    for (auto& trans_ptr : current_transition_paths) {
        transNo++;
        int transId = trans_ptr->getTransitionId();
        string str1 = "e" + to_string(transId) + "00" + to_string(transNo);
        fileout << "    <param name=\"" << str1 << "\" type=\"label\" local=\"false\" />" << endl;
    }

    /* Setting locations in the xml */
    int locsNo = 0;
    for (auto& loc_ptr : current_location_paths) {
        locsNo++;
        int locId = loc_ptr->getLocId();
        string str2 = to_string(locId) + "00" + to_string(locsNo);
        fileout << "    <location id=\"" << str2 << "\" name=\"loc" << str2 << "\">" << endl;
        // ... [insert additional location data here]
        fileout << "    </location>" << endl;
    }

    /* Setting transitions in the xml again */
    transNo = 0;
    locsNo = 1;
    auto locIter = current_location_paths.begin();
    for (auto& trans_ptr : current_transition_paths) {
        transNo++;
        int transId = trans_ptr->getTransitionId();
        string str1 = "e" + to_string(transId) + "00" + to_string(transNo);
        int source = (*locIter)->getLocId();
        string str2 = to_string(source) + "00" + to_string(locsNo);
        std::advance(locIter, 1);
        int target = (*locIter)->getLocId();
        locsNo++;
        string str3 = to_string(target) + "00" + to_string(locsNo);
        fileout << "    <transition source=\"" << str2 << "\" target=\"" << str3 << "\">" << endl;
        fileout << "      <label>" << str1 << "</label>" << endl;
        // ... [insert additional transition data here]
        fileout << "    </transition>" << endl;
    }

    fileout << "  </component>" << endl;
    fileout << "</sspaceex>" << endl;

    fileout.close();

    return str; // returning path to xml file
}

