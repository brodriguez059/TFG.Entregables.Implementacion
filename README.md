# Formalización del cálculo PS en Isabelle/HOL

Este proyecto contiene las diferentes implementaciones necesarias para la definición y demostración de la completitud del cálculo PS:
- El lenguaje _Conjunctive Positive Logic_ (CPL)
- El problema _Quantified Constraint Satisfaction Problem_ (QCSP)
- El propio cálculo PS definido en [Verified Model Checking for Conjunctive Positive Logic](https://dx.doi.org/10.1007/s42979-020-00417-3)

Se ha desarrollado con el fin de ser presentado como el Trabajo Fin de Grado de Baldwin Rodríguez, habiendo sido éste dirigido por Montserrat Hermo y Javier Álvez.

Los ficheros del proyecto siguen la siguiente estructura y definición:
- `CPL_Syntax.thy`: La sintaxis del fragmento de la lógica CPL.
- `CPL_Semantic.thy`: La semántica de los modelos del problema QCSP.
- `CPL_Proof_System.thy`: Los juicios, evaluaciones, una serie de utilidades básicas que trabajan sobre estos objetos y el cálculo PS como tal.
- `CPL_Completeness.thy`: Las demostración de completitud del cálculo PS.
