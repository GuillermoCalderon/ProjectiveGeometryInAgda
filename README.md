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
propositions and theoremes in the formalization:

Definitions
===========

+  [Apartness Relation](/Relation/Binary/Apartness.agda#L16)
+  [Setoids](/Relation/Binary/Apartness.agda#L51)
+  [Projective plane](/ProjectivePlane.agda#L132) (*a la Mandelkern*)
+  [Complete n-point](/ProjectivePlane/CompleteNPoint.agda#L26)
+  [Triangle](/ProjectivePlane/CompleteNPoint/Triangle.agda#L128)
+  [Quadrangle](/ProjectivePlane/CompleteNPoint/Quadrangle.agda#L33)
+  [Perspective triangles wrt a center](/ProjectivePlane/CompleteNPoint/Triangle/Perspective.agda#L62)
+  [Perspective triangles wrt an axis](/ProjectivePlane/CompleteNPoint/Triangle/Perspective.agda#L75)
+  [Desarguesian plane](/ProjectivePlane/Desargues.agda#L12)
+  [Fanoian plane](ProjectivePlane/Fano.agda#L46)
+  [Dual projective plane](ProjectivePlane/Duality.agda#L116)
+  [Harmonic configuration](/ProjectivePlane/Harmonic/Base.agda#L28)
+  [Harmonic conjugate](/ProjectivePlane/Harmonic/Base.agda#L169)
+  [van Dalen's projective plane](/VanDalen/Outside.agda)
+  [von Plato's appartness geometry](/VonPlato/ApartnessGeometry.agda)
+  [von Plato's projective plane](/VonPlato/ProjectiveGeometry.agda)

Propositions
============

+ Basic propositions of incidence
+ Principle of Duality
+ Desargues dual theorem
+ Fano dual theorem
+ Existence of the harmonic conjugate
+ Uniquenes of the harmonic conjugate
+ Equivalence with van Dalen system
+ Equivalence with von Plato system
