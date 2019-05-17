# finis
An Ab Initio Transform to Python compiler

## Project Goal
It has been shown that Ab Initio graphs (the graph structure and transformations) can be
compiled into Python code. However, there has not been any proof showing the semantics preservation of
such a compiler.  The goal of my project is to prove the semantics preservation of a Ab Initio Transform to Python compiler.  
Since I was limited in time, this proof is over a subset of the Ab Initio transformation language.
The subset of grammar I used is given in the following [file](./AbInitioGrammar.g4). I first modeled
this subset and it's interpretation in Coq, [found in this file](./transforms.v). I also modeled the equivalent subset of Python
3 in Coq, [found in this file](./python.v). I then wrote a compiler between the two and proved the semantics preservation property
of this compiler, [found in this file](./compiler.v).

## Ab Initio Background
Ab Initio is a graphical user interface (GUI)-based data extract, transform, and load (ETL) tool. Ab
Initio ETL jobs are represented as a directed graph.  Each vertex in the graph is a Ab Initio component.
Components can be comprised of inputs ports, outputs ports, transformations and various metadata parameters
of the component. Transformations are coding in Ab Initio using Ab Initio's own language. An example of a transform is below.
```
begin
  let int i;
  let decimal("\|")[int] newamt;
  newamt = for(i, i < in.total_count) : if (!isblank(in.amount[i])) in.amount[i];

  out.len :: length_of(newamt);
  out.amount :: newamt;
end ;
```
The data transformations, structural elements of the graph and graphical information are all stored in a single
file. One grammars is used to represent the structural elements of the graph and another to represent the
transformations.

## Files in this project
* [AbInitioGrammar.g4](./AbInitioGrammar.g4): Defines the grammar of Ab Initio Transformation used in this project
* [PythonGrammar.g4](./PythonGrammar.g4): Defines the grammar of python used in this project
* [imports.v](./imports.v): Imports and common features used throughout the program
* [transforms.v](./transforms.v): This file describes the Ab Initio Transform language in coq.  In
 this file, I define the language's syntax, and evaluation.
* [python.v](./python.v): This file describes the python language in coq.  In
this file, I define the language's syntax, and evaluation.
* [compiler.v](./compiler.v): Contains the compiler from Ab Initio to Python.  The first set of proofs in this file prove that the code executes to the same value as Ab Initio code or as compiled code to python.  The last proof proves that the code ends in the same state when run as Ab Initio code or as compiled code to python.

## Challenges
* _Picking a subset of the language to compile_: Ab Initio commands are mainly based on
transformations on a data table.  I was not sure how I would represent a data frame in coq.  Because of this, I tried to start with a portion Ab Initio language that would work with basic
types.  This ended up mainly being arithmetic or boolean expressions, which were already close to how they are represented in Python.  Because of this, much of the compiler is simple;
there's not much difference between the Ab Initio and python implementation.

* _Allowing different types to be returned_: One interesting different between Ab Initio
python is how they implement loops.  In Ab Initio, for loops and while loops always return a list (or vector as called in Ab Initio).  Because of this, I wanted to add lists as a value to my
compiler.  Since fixpoints in coq can only return one type of value, I had to create a type
to wrap around all the values that would be returned.  At first, I tried to define separate
types for Ab Initio and for python.  This was made proving equivalence between the two languages
difficult, as they were always returning different types.  It also made proving equivalence between
the states difficult, as the states mapped to different types.  To mitigate this problem, I
created a shared type (`pvalue`) to represent values returned from both languages.
