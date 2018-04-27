Formalizing Constructive Projective Geometry in Agda
=======================================================

Abstract
---------

We present a formalization of Projective Geometry in the
proof assistant and programming language Agda.
We formalize a recent development on constructive Projective Geometry
which has been showed appropriate to cover most traditional topics in
the area applying only constructively valid methods. In addition, the
equivalence with other well-known constructive axiomatic systems for
projective geometry is proved and formalized.
The implementation covers a basic fragment of intuitionistic synthetic
Projective Plane Geometry including the axioms, principle of duality,
Fano and Desargues properties and harmonic conjugates.
We describe as an illustrative example, the implementation of a complex
and large proof which appears partially and vaguely described in the
literature; namely the uniqueness of the harmonic conjugate.
The most important details of our implementation are described and
we show how to take advantage of several interesting properties of Agda
such as modules, dependent record types, implicit arguments and instances
which result very helpful to reduce the typical verbosity of formal proofs.

Description
------------

This repository provides the Agda code relative to the paper.

This code was compiled with:

+  Agda version 2.6.0
+  Standard library 0.14

Author
------
Guillermo Calderon (calderon@fing.edu.uy)

Date
-----

April 2017

Contents
---------

- `Relation.Binary.Apartness.agda`  
   Definition of the apartness relation and constructive setoids.
-  `Data.Fin.Setoid.agda`   
   Definition of a decidable setoid for `Fin n`.
- `ProjectivePlane.agda`  
   Definition of the structure `ProjectivePlane` which represents the constructive
   axiomatization of the *projective plane*.
   
   
