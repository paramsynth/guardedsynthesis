# Guarded Parameterized Bounded Synthesis #

This prototype for the synthesis of guarded systems is based on the Party tools by Ayrat Khalimov, Swen Jacobs, and Roderick Bloem. 
Please also read https://github.com/5nizza/Party/blob/master/README.md

## Requirements ##
- python3
  + python-graph-core
- Z3 4.3.1 with API for python
- ltl3ba 1.0.2

## Directory Structure ##
- The `src` directory contains the implementation.
- The `benchmarks` directory includes example LTL specification files.

## Configuration ##
Please set the paths for the required tools (Z3, lzl3ba) in config.py.

## Run the Prototype ##
- Run `python3 gp_bosy.py --help` in order to get further information about how to run the program

## Example Setup (tested on Debian wheezy) ##
1. Create folder structure

   ```
   mkdir -p gp_bosy/utils
   mkdir -p gp_bosy/guardedsynthesis  # clone repository...
   ```

2. Install required packages from Debian repository
   ```
   sudo apt-get install build-essential libbdd-dev python3 python3-pip
   ```
3. Build z3
   1. Move to the `utils` directory
   2. Install the newest git version [2]
   3. Checkout the unstable branch of z3 and start the build [3]
4. Build ltl3ba

   ```
   cd utils
   wget http://downloads.sourceforge.net/project/ltl3ba/ltl3ba/1.0/ltl3ba-1.0.2.tar.gz
   tar xzf ltl3ba-1.0.2.tar.gz
   cd ltl3ba
   make
   cd ..
   ```
5. Get required python packages

   ```
   pip3 install python-graph-core
   ```
6. Set paths in config.py

   ```
   Z3_PATH="/some_path/utils/z3/build/z3"
   LTL3BA_PATH="/some_path/utils/ltl3ba-1.0.2/ltl3ba"
   DEFAULT_TARGET_FOLDER="/path_where_synthesis_results_should_be_saved/
   ```
7. Start our prototype

   ```
   PYTHONPATH=$PYTHONPATH:/some_path/utils/z3/build/ python3 gp_bosy.py
   ```
   Setting the `PYTHONPATH` is only necessary if you did not install z3.

   Example call: `python3 gp_bosy.py -t conjunctive_guards --min-bound 2 2 --max-increments 5 --instances 1 5 specification.ltl` 

   * Disjunctive system with 2 templates
   * 1 instances of the first template
   * 5 instances of the second template
   * Template sizes are at least (2,2) and at most (7,7)

## Authors ##
Guarded Parameterized Bounded Synthesis implemented by Simon Ausserlechner based on the
Parameterized Bounded Synthesis tool by Ayrat Khalimov, Swen Jacobs, Roderick Bloem, TU Graz.

## License ##
Free for any use with references to the original authors.

## References ##
[1] https://raw.githubusercontent.com/5nizza/Party

[2] http://z3.codeplex.com/wikipage?title=Git%20HTTPS%20cloning%20errors

[3] http://z3.codeplex.com/wikipage?title=Building%20the%20unstable%20%28working-in-progress%29%20branch
