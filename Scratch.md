I think tying the argument form replacement of typed contextual equive terms sucinctly captures what is problematic about most dependently typed languages.  However there are risks involved:
* for instance this should be allowed
```
x |- head x (rep [1+x])
x |- head x (rep [x+1])
```
* CE may not be possible with with type level computation that happens under binder, since it may mess up bi directional inference
```
x |- (...: (F:Nat->*) -> F x) (\_->                  Nat -> Nat ) 7
x |- (...: (F:Nat->*) -> F x) (\x-> case x of 0   => Nat -> Nat
                                             |S _ => Nat -> Nat ) 7
```
  * now things get very subtle, since with enouh annotations you can make this work, and you still have access to all the equalities as before.
    * it may be possible to make this strict (though this may not be possible):
      * by requaireing type annotations at such type computations
	  * by requireing elaboration at to solve the annotation?
x |- ((...: (F:Nat->*) -> F x) (\x-> case x of 0   => Nat -> Nat
                                             |S _ => Nat -> Nat ) : Nat -> Nat) 7

* even at simple types!
```
rep x = case x of
  0   => Nat
  S _ => Nat -> Nat 

x , f : (X:*)-> X  |- f (head x (rep [1+x])) 7
```

* also consider wierd data like
evilnat
z : bot -> evilnat
s : evilnat -> evilnat

now any type level elimination 
... |- case s x of 
		  z -> 1
		  s _ -> 2 

May be problematic since it is not reflected by runtime information? since the context can never be witnessed this is not really an issue


											 
* since the CE is indexed by types there must be some work to assure it is well founded
* adding solve to the language makes the visible equivelence finer than expected (still need an example of this)
* still undecidable, wich means in practice there will still be equivelent computations that when substituted take the user out of the cutoff (these are pretty contrived)  
* `solve` has a complicated relationship with non-termination.  especially here, where nontermination should be considered defective behavour, but is tolaraed for user convinence


Since some changes have been made since this was last worked out:
* search proscedure now needs to handle symbolic types

