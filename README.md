# Nyan

My experimentation with defining categories from scratch in Coq. 

## Contents

- Theory
  + [Category.v](./Theory/Category.v): typeclass definition of categories
  + [Arr.v](./Theory/Arr.v): given a category, the category of its arrows
  + [Dual.v](./Theory/Dual.v): given a category, the category with reversed arrows
  + [Product.v](./Theory/Product.v): product of two categories
  + [Ism.v](./Theory/Ism.v): various types of morphisms
  + [Functor.v](./Theory/Functor.v): functors and natural transformations/isomorphisms
- Examples
  + [Set.v](./Examples/Set.v): Coq's `Set` as a category
  + [Poset.v](./Examples/Poset.v): the category **Poset** and posets as categories
  + [Monoid.v](./Examples/Monoid.v): the category **Mon** and monoids as categories
  + [IdentityFunctor.v](./Examples/IdentityFunctor.v): the identity functor as a natural isomorphism
  + [Maplist.v](./Examples/Maplist.v): Coq's List.map as a functor, with List.rev as a natural isomorphism

## References

Heavily borrows from 
- https://www-sop.inria.fr/marelle/Coq7_workshop/Coq7_submission_5.pdf
- https://github.com/jwiegley/category-theory

Examples are taken from _Basic Category Theory for Computer Scientists_ 
