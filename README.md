# tarjan-mercury
A small pure implementation of Tarjan's strongly connected components algorithm (for use in detecting cycles) in the Mercury logical programming language.

Implementation is done by passing along a state variable through the program. Very tedious, but I needed this working. 

Its probably not very efficient, but if I did not mess anything up, it should find all cycles within O(V + E) time. If I did mess something up, do let me know. 
