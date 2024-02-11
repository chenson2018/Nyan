# Nyan

My experimentation with defining categories from scratch in Coq. 

## Contents

- Theory
  + [Category.v](./Theory/Category.v): typeclass definition of categories
  + [Arr.v](./Theory/Arr.v): given a category, the category of its arrows
  + [Dual.v](./Theory/Dual.v): given a category, the category with reversed arrows
  + [Ism.v](./Theory/Ism.v): various types of morphisms
- Examples
  + [Set.v](./Examples/Set.v): Coq's `Set` as a category
  + [Poset.v](./Examples/Poset.v): The category **Poset** and posets as categories
  + [Monoid.v](./Examples/.v): The category **Mon** and monoids as categories  

## References

Heavily borrows from 
- https://www-sop.inria.fr/marelle/Coq7_workshop/Coq7_submission_5.pdf
- https://github.com/jwiegley/category-theory

Examples are taken from _Basic Category Theory for Computer Scientists_ 
