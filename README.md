# tarjan-mercury
A small pure implementation of Tarjan's strongly connected components algorithm (for use in detecting cycles) in the Mercury logical programming language. 

The cycles can be detected using the ~tarjan(in, in, out)~ predicate. It is polymorphic and should support vertices of any type (as long as it can be compared/unified normally). Edges are represented by a list of pairs of verticies.

Implementation is done by passing along a state variable through the program. Very tedious, but I needed this working. 

Its probably not very efficient, but if I did not mess anything up, it should find all cycles within O(V + E) time. If I did mess something up, do let me know. 
