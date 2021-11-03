# verified-monads-agda
Monads with proof of correctness, in `Agda`.

Continuation and Reader aren't complete, in the following sense; since `Agda` doesn't have extensional equality, we can't prove propositions like

`prf : {A B : Set} \to {f g : A \to B} \to f \== g`

we can, however, explicitly prove them in this form:

`prf : {A B : Set} \to {f g : A \to B} \to`

`      (x : A) \to f x \== g x`

This means, however, that we need something like

`property_\phi : {F : Set \to Set} \to {A B : Set} \to`

`                (f : A \to B) \to (g : A \to B) \to`

`                ((x : A) \to f x \== g x) \to`

`                (y : F A) \to \phi f x \== \phi g x`
				 
for a large class of functions `\phi : (A \to B) \to F A \to F B`.
The trick used here is to embed this function as part of the definition of "functor".

This doesn't work for the Reader and Continuation monads, since their values actually embed functions: the `y : F A` would be a function, hence propositions in that form are, again, unprovable. Curiously, all other results about them (the functor structure and the monad structure) seem to be directly provable (even if in the second case, the result probably relies on the unproven assumption that such a property holds: I'm not sure, since both instances of that function
have been left as a hole).

