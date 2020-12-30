**Note: I have wasted far too much time on this, so I am going to stop for now**

Graphs highlight some issues with agda style-programming:
* seem to requaire completeness predicates that are combersome.  You can't simply offer a function giving a list of outgoing edges, you need to include a proof that all other edges are impossible
* not stricty inductive
* reasonalbe to support very different encodings (edge matrix, edge list, functional), but hide behind a standard interface
* unclear how much static information should be included (though indexing by number of verticies seems reasonable).  
* have many flavors of graph formalism that make interface creation hard: labled-graphs, weighted-graphs, directed-graphs, directed-acyclic graphs, multi-graphs, self loops...
* I suspect it is very hard to come up with an interface to different graph implementations that exposes enough properties to prove realistic correctness properties of implementation agnostic functions
* Admit isomorphisms that are annoying to formalize and computationally difficult to discover

# Encodings

## Adjacency list
```agda
record Graph {n : ℕ} : Set where
  field
    edge : Vec (List (Fin n)) n
open Graph
```
* does not encode order, so that graph equality is not supported

## "functional" encoding
```agda
record Graph {n : ℕ} : Set where
  field
    edge : (from : Fin n) -> (to : Fin n) -> Bool 
open Graph
```
* could, in principle, hide a more efficent encoding
* equality issues
  * with function extentionallity, does identify reasonable equalitities
  * But since Agda lacks function extentionality the normal equality predicates will be unprovable
    * since the graph is indexed by the number of verticies, something like equalities should be recoverable in something like a setoid
  * There will also be definitional issues
* some reaosnable constraints like self connections will not be enforeced


## Matrix encoding
```agda
record Graph {n : ℕ} : Set  where
  field
    edge :  Vec (Vec Bool n) n
open Graph
```
* has the correct ground deffinitional equalities

## Other flavors
* without a static bound on the number of verticies, termination would be hard to prove
  * adjacency would be ok
  * the function encoding would allow infinite graphs
  * the matrix encoding would be difficult to maintain


# other functional graph theory work
### Agda examples
http://dominic-mulligan.co.uk/wp-content/uploads/2019/02/itp16.pdf
  
### Scala graph library
* http://www.scala-graph.org/

### Haskell graph library
* https://dl.acm.org/doi/10.1145/3122955.3122956
* https://github.com/snowleopard/alga-paper
* https://github.com/algebraic-graphs/agda/tree/master/src
  * not indexed by number of vert
  * heavily axiomatic?
  * turn some of their axioms into checks

general functional 

## TODO:
* shortest path (The only way forward I see is through self-similar multi graphs that can encode the intermediate state)
* max flow/min cut
* Arseniy Alekseyev. 2014. Compositional approach to design of digital circuits. Ph.D. Dissertation. Newcastle University
