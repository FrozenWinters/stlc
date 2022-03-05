# Categorical glueing for simply typed lambda calculus

This formalisation mostly follows the 1995 paper *Categorical reconstruction of a reduction free normalization proof* by Altenkirch at al.

## Reading Order

### Part I : Objective Metatheory

#### Defining the Structures

1. [lists](lists.agda): Defines the basic data patterns that we see in contextual categories (`𝐶𝑡𝑥`, `𝑇𝑚𝑠`, and `𝑉𝑎𝑟`)
2. [contextual](contextual.agda): Gives the organising definition behind this implementation; everything is this project relies on contextual structures
3. [ccc](ccc.agda): Defines what it means for a contextual category to be cartesian closed, and gives consequences of the structure
4. [functor](functor.agda): Defines contextual functors, constructs composition, and says what it means for a CF to preserve CCC structures

#### Construstions
5. [psh](psh.agda): Defines a contextual cartesian closed category of presheaves
6. [normal](normal.agda): Defines normal an neutral terms, and related presheaves
7. [twgl](twgl.agda): Defines a contextual category of glueings. Shows that any glueing gives rise to a normal form and equality proof
8. [twglccc](twglccc.agda): Establishes the contextual cartesian closedness of glueings
9. [norm](norm.agda): Establishes that any initial syntactic category has normalisation

### Part II : Syntax

10. [syn](syn.agda): Defines the syntactic contextual category
11. [eliminator](eliminator.agda): Establishes the initiality of syntax
12. [tests](tests.agda): Some applications of our results
