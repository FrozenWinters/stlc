# Categorical glueing for simply typed lambda calculus

This formalisation mostly follows the 1995 paper *Categorical reconstruction of a reduction free normalization proof* by Altenkirch at al.

## Reading Order

### Part I : Objective Metatheory

#### Defining the Structures

1. [lists](lists.agda): Defines the basic data patterns that we see in contextual categories (`𝐶𝑡𝑥`, `𝑇𝑚𝑠`, and `𝑉𝑎𝑟`)
2. [contextual](contextual.agda): Gives the organising definition behind this implementation; everything is this project relies on contextual structures
3. [ccc](ccc.agda): Defines what it means for a contextual category to be cartesian closed, and gives consequences of the structure
4. [cart](cart.agda): Defines what it means for a category to be cartesian closed and shows that this gives rise to a contextual structure

#### Construstions
5. [normal](normal.agda): Defines normal an neutral terms
6. [psh](psh.agda): Defines preshavess as a cartesian closed category and uses `cart` to construct a contextual category `𝒫𝒮𝒽`
8. [presheaves](presheaves.agda) Constructs the presheaves `TM`, `NE`, and `NF`
9. [twgl](twgl.agda): Defines a contextual category of glueings. Shows that any glueing gives rise to a normal form and equality proof
10. [twglccc](twglccc.agda): Establishes the contextual cartesian closedness of glueings
11. [norm](norm.agda): Establishes that any initial syntactic category has normalisation

### Part II : Syntax

11. [syn](syn.agda): Defines the syntactic contextual category
12. [eliminator](eliminator.agda): Establishes the initiality of syntax
13. [tests](tests.agda): Some applications of our results
