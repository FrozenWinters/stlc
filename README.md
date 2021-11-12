# Categorical glueing for simply typed lambda calculus

This formalisation mostly follows the 1995 paper *Categorical reconstruction of a reduction free normalization proof* by Altenkirch at al.

## Reading Order

1. [lists](lists.agda): Defines the basic data patterns that we see in contextual categories (`𝐶𝑡𝑥`, `𝑇𝑚𝑠`, and `𝑉𝑎𝑟`).
2. [contextual](contextual.agda): Gives the organising definition behind this implementation. Everything is this project relies on contextual structures.
3. [ccc](ccc.agda): Defines what it means for a contextual category to be cartesian closed, and gives consequences of the structure.
4. [cart](cart.agds): Defines what it means for a category to be cartesian closed and shows that this gives rise to a contextual structure.
5. [ren](ren.agda): Defines STLC types (`Ty`) and the contextual category `ρεν` of renamings, as well as its ambient category `REN`.
6. [psh](psh.agda): Defines preshavess as a cartesian closed category and uses `cart` to construct a contextual category `𝒫𝒮𝒽`.
7. [syn](syn.agda): Defines the syntactic contextual category as well at the preshaef of terms and some related lemmas.
8. [eliminaotr](eliminator.agda): Constructs a contextual functor from syntax into any other contextual category.
9. [normal](normal.agda): Defines the preshaves of normal and neutral terms.
10. [twgl](twgl.agda): Defines a contextual category of glueings. Shows that any glueing gives rise to a normal form and equality proof.
11. [twglccc](twglccc.agda): Establishes the contextual cartesian closedness of glueings.
12. [norm](norm.agda): Uses the eliminator on the catesian structure of glueings.
13. [tests](tests.agda): Contains some tests.
