# Outline
* Introduction
  * motivating examples
  * full spectrum
  * equality
* A Cardelli style type thoery
  * Why
    * programmers do not care abut non-termination
    * in some sense the simplest, most predictable option
    * termination and well foundedness concerns can still asuaged, but they don't get in the way
  * formal account
    * without data
    * with data
  * Properties
    * subject reduction
  * counter examples
    * non termination
  * How can termination also be asserted(?)
  * Equality
    * consevative, characteristic of ITTs (and the implemenation of ETTs)
  * History
    * Russels paradox?
    * Martin Lof's first attempt
    * Cardelli's revision embracing the non-termination
    * theory
    * implementaitons
      * table? - doe this in sheets ant remove some colums
* A Cardelli style type thoery with dynamic equality and Blame
  * Why
    * dependently typed equality is subtle/akward
  * formal system
  * Properties
    * cast soundness to track blame
  * History
    * contracts/blame
    * things that sound like this but arn't?
* elaboration (should it be it's own chapter?)
  * Properties
    * relation to the ideal system
  * History
    * contracts/blame
    * gradual typing (?)
* Runtime proof search
* Symbolic testing
* large worked example
* History (?)
* Future work
  * fully prolog like  nondeterminism
  * Effects in genral
  * whatever implementation is not yet done
    * parrtern matching 
    * motive inference
  * whatever proof stuff is not yet done
  * whatever formal developments are not yet done
  * effects
* Conclusion

# Dertailed plan
* Thoughly review all papers related to the cardelli style stuff
  * All references down playing it in the 80s paper
  * Implementations
    * actually track down a copy of Cyann to run?
    * actually run the different versions of zombie associated with each paper, run them
    * agda, idris, coq wioth the appropriate compiler flags

