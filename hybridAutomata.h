/*
 * Hybrid_Automata.h
 *
 *  Created on: 09-Jul-2014
 *      Author: amit
 */

#ifndef HYBRID_AUTOMATA_H_
#define HYBRID_AUTOMATA_H_

#include <list>
#include <map>
#include <boost/shared_ptr.hpp>
#include "counterExample/structuralPath.h"
#include <bits/stdc++.h>
#include "core/hybridAutomata/location.h"
#include "core/math/matrix.h"
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/adjacency_matrix.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/named_function_params.hpp>
#include <boost/graph/properties.hpp>
#include <boost/graph/adjacency_list.hpp>
//#include <application/replayPath.h>
#include <counterExample/structuralPath.h>
#include <core/hybridAutomata/transition.h>

//#include <boost/property_map/associative_property_map.hpp>
#include <map>


using namespace std;

class hybrid_automata : public var_to_index_map {
	std::map<int, location::ptr> list_locations;		//mapping a list of locations based on the key=loc_id
	location::ptr initial_loc;
	int dimension;
public:
	typedef boost::shared_ptr<hybrid_automata> ptr;
	hybrid_automata();

	hybrid_automata(std::map<int, location::ptr>& list_locs, location::ptr init_loc,
			int dim);
	/* returns a boost pointer */
	ptr getSharedPtr(){
		return ptr(this);
	}
	void addInitialLocation(location::ptr& initLoc);

	/* sets the initial location from its id. Silently does nothing
     * if the init_id is not in the id to location map.
	 */
	void setInitialLoc(int init_id);
	
	/*
	 * get the adjacency matrix representation of the hybrid automata object..
	 */
//	math::matrix<int> getGraph();
	math::matrix<transition::ptr> getGraph();


//	void getGraph();


	/*
	 * get reverse graph
	 */
//	math::matrix<int> getReverseGraph(const math::matrix<int>& originalMatrix);
	/*
	 * generate boost adjacency matrix from getGraph adjacency matrix
	 */
	typedef boost::adjacency_matrix<boost::directedS, int> BoostAdjacencyMatrix;
	BoostAdjacencyMatrix bglGraph(const math::matrix<int>& mat);

	typedef boost::property<boost::edge_name_t, transition::ptr> EdgeProperty;
	typedef boost::adjacency_matrix<boost::directedS, int, EdgeProperty> BoostAdjacencyMatrixWithTransitions;



	/*
	 * finds all dfs paths between source and destination nodes
	 */

//	typedef boost::graph_traits<BoostAdjacencyMatrix>::vertex_descriptor Vertex; // boost graph vertex data type

	typedef boost::graph_traits<BoostAdjacencyMatrixWithTransitions>::vertex_descriptor Vertex;

	BoostAdjacencyMatrixWithTransitions bglGraph(math::matrix<transition::ptr>);

//	void bglDFSpaths(BoostAdjacencyMatrix adjacencyMatrix, Vertex start, Vertex end, int max_depth);
	void bglDFSpaths(BoostAdjacencyMatrixWithTransitions adjacencyMatrix, Vertex start, Vertex end, int max_depth);

/*
	 * Print the adjacency matrix formed from getGraph()..
	 */
//	void printGraph(const math::matrix<int>& mat);

	void printGraph(const BoostAdjacencyMatrixWithTransitions& graph);

	/*
	 * Generate a path with location ptrs from location id as input.
	 */
	struct PathInfo {
	    std::vector<location::const_ptr> locations;      // Store location pointers
	    std::vector<transition::ptr> transitions;        // Store transition pointers
	};


	structuralPath::ptr createStructuralPath(const std::vector<location::const_ptr>& locations,
	                                   const std::vector<transition::ptr>& transitions) ;

	void generateXmlAndCfgFromPath(
	    const std::vector<location::const_ptr>& currentPathLocations,
	    const std::vector<transition::ptr>& currentPathTransitions,
	    int& pathNo);

	string generateKey(const std::vector<location::const_ptr>& subPathLocations);

	void generatecfg(fstream& file1, structuralPath::ptr path, string file_path, string model, int pathNo, bool agent_model);

	string generateXml(fstream& file, structuralPath::ptr path, string file_path, string model, int pathNo);

	bool cH_Replay(const string& str);

	std::pair<vector<int>, vector<int> > cA_Replay(string str);


	location::ptr getInitialLocation() const;

	//returns the location from the list of locations with location_ID as the input parameter
	location::const_ptr getLocation(int Loc_ID) const;

	//returns the location from the list of locations with location_ID as the input parameter which can be manipulated.
	location::ptr getLocationNew(int Loc_ID); //Sajid Sarwar

	/* returns the location from the list of locations with locName */
	location::const_ptr getLocation(string locName) const;

	void addMappedLocationsList(std::map<int, location::ptr>& mapped_location_list);

	void addLocation(location::ptr& loc);	//inserts location into its correctly mapped key
	int getDimension() const;
	void setDimension(int dimension);

	/*
	 * Returns the total number of Locations in the hybrid automata with ID = 1 to returned size
	 */
	int getTotalLocations() const {
		return list_locations.size();
	}
	
	std::map<int, location::ptr> getAllLocations() const {
		return list_locations;
	}
	
	/**
	 * Returns all structural paths in the HA starting from the initial location and ending at the
	 * forbidden_location (passed as a parameter). The paths of length at-most depth are considered.
	 *
	 */
	std::list<structuralPath::ptr> getStructuralPaths(unsigned int forbidden_loc_id, unsigned int depth);

	/**
	 * A sat-based path enumeration procedure.
	 * Returns the number of paths enumerated from src to dst of length bounded by depthBound
	 */
	unsigned int satEnumPaths(unsigned int forbidden_loc_id, unsigned int depth);

	std::list<structuralPath::ptr> findAllPaths(int src, int dst, int depthBound);

	void printPath(std::vector<int>& path);

};

#endif /* HYBRID_AUTOMATA_H_ */
