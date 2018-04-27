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

In this section, we provide links to the most important definitions, lemmas,
propositions and theoremes of the formalization:

## Definitions

+  [Apartness Relation](/Relation/Binary/Appartness.agda)
+  Setoids
+  [Projective plane](/ProjectivePlane.agda) (*a la Mandelkern*)
+  Complete n-point
+  Triangle
+  Quadrangle
+  Desarguesian plane
+  Fanoian plane
+  Dual projective plane
+  Harmonic configuration
+  Harmonic conjugate
+  van Dalen's projective plane
+  von Plato appartness geometry
+  von Plato projective plane

## Propositions

+ Basic propositions of incidence
+ Principle of Duality
+ Desargues dual theorem
+ Fano dual theorem
+ Existence of the harmonic conjugate
+ Uniquenes of the harmonic conjugate
+ Equivalence with van Dalen system
+ Equivalence with von Plato system
