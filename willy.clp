;*****************************************
; Autores:
; Historial de cambios:
;  - Fecha: mejoras/cambios
;*****************************************

;==========================================
;Modulo de MAIN, pasa el control del programa a myMAIN

(defrule MAIN::passToInicialModule
	=>
	(focus myMAIN))
	
;==========================================
;Modulo de myMAIN, controla la iteracion de los modulos y el fin de ejecucion

(defmodule myMAIN (import MAIN deftemplate ?ALL) (export deftemplate ?ALL))

(deftemplate STOP
	(slot state)
)

(defrule passToInicialRule
	=>
	(assert (next_modulo Percepcion))
	(assert (STOP (state false))))

(defrule passToPercepcion
	?h <- (next_modulo Percepcion)
	(not(STOP (state true)))
	=>
	(retract ?h)
	(assert (next_modulo Inferencia))
	(focus Percepcion))
	
(defrule passToInferencia
	?h <- (next_modulo Inferencia)
	(not(STOP (state true)))
	=>
	(retract ?h)
	(assert (next_modulo Movimiento))
	(focus Inferencia))
	
(defrule passToMovimiento
	?h <- (next_modulo Movimiento)
	(not(STOP (state true)))
	=>
	(retract ?h)
	(assert (next_modulo Percepcion))
	(focus Movimiento))


;==========================================
;Modulo de Percepcion, se observan las casillas circundantes

(defmodule Percepcion (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (export deftemplate ?ALL))

(deftemplate casilla					;Informacion casillas (1=true 0=false)
	(slot x)								;Posicion x de la casilla
	(slot y)								;Posicion y de la casilla
	(slot visited (default 0))		;Casilla visitada
	(slot safe (default 0))			;La casilla es totalmente segura
	(slot alien (default 0))		;Hay alien en la casilla
	(slot hole (default 0))			;Hay agujero en la casilla
	(slot pull)							;Se percibe empuje
	(slot noise)						;Se percibe sonido
	(slot danger)						;La casilla tiene un peligro seguro sin especificar cual
)
(deftemplate willy
	(slot x)
	(slot y)
)

(defrule firstState
	(not (casilla (x ?)(y ?) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
=>
	(assert (casilla (x 0) (y 0) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 0) (danger 0)))
	(assert (willy (x 0) (y 0)))
)

(defrule actualState
	(willy (x ?x) (y ?y))
	?h1<-(casilla (x ?x) (y ?y) (visited 0) (safe ?) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(retract ?h1) 
	(assert (casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d)))
)

;----------------------------------------------------------------------------
;Crea las casillas circundantes si no existen

(defrule surroundingsX
	(willy (x ?x) (y ?y))
	(x ?mX)
	(not (casilla (x =(+ ?mX ?x)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
=>
	(assert (casilla (x (+ ?mX ?x)) (y ?y) (visited 0) (safe 0) (alien 0) (hole 0) (pull 0) (noise 0) (danger 0)))
)

(defrule surroundingsY
	(willy (x ?x) (y ?y))
	(y ?mY)
	(not (casilla (x ?x) (y =(+ ?mY ?y)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
=>
	(assert (casilla (x ?x) (y =(+ ?mY ?y)) (visited 0) (safe 0) (alien 0) (hole 0) (pull 0) (noise 0) (danger 0)))
)

;----------------------------------------------------------------------------
;Deteccion de peligros casilla actual

(defrule detectNoise
	(declare (salience 1))
	(willy (x ?x) (y ?y))
	(or (percepts Noise) (percepts Pull Noise) (percepts Noise Pull))
	?h1<-(casilla (x ?x) (y ?y) (visited 0) (safe ?s) (alien ?a) (hole ?h) (pull ?p) (noise 0) (danger ?d))
=>
	(retract ?h1)
	(assert (casilla (x ?x) (y ?y) (visited 0) (safe ?s) (alien ?a) (hole ?h) (pull ?p) (noise 1) (danger ?d)))
)

(defrule detectPull
	(declare (salience 1))
	(willy (x ?x) (y ?y))
	(or (percepts Pull) (percepts Pull Noise) (percepts Noise Pull))
	?h1<-(casilla (x ?x) (y ?y) (visited 0) (safe ?s) (alien ?a) (hole ?h) (pull 0) (noise ?n) (danger ?d))
=>
	(retract ?h1)
	(assert (casilla (x ?x) (y ?y) (visited 0) (safe ?s) (alien ?a) (hole ?h) (pull 1) (noise ?n) (danger ?d)))
)

;----------------------------------------------------------------------------
;Determina si las casillas de alrededor son seguras

(defrule lookAroundX
	(declare (salience -1))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull 0) (noise 0) (danger ?))
	(x ?mX)
	?h1<-(casilla (x =(+ ?mX ?x)) (y ?y) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(retract ?h1)
	(assert(casilla (x =(+ ?mX ?x)) (y ?y) (visited ?v) (safe 1) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d)))
)

(defrule lookAroundY
	(declare (salience -1))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull 0) (noise 0) (danger ?))
	(y ?mY)
	?h1<-(casilla (x ?x) (y =(+ ?mY ?y)) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(retract ?h1)
	(assert(casilla (x ?x) (y =(+ ?mY ?y)) (visited ?v) (safe 1) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d)))
)

;----------------------------------------------------------------------------
;Se traducen las direcciones a valores numericos para operar con coordenadas

(defrule direction
	(directions $? ?direction $?)
=>
	(assert (dir ?direction))
)

(defrule convertionNorth
	?h1<-(dir north)
=>
	(retract ?h1)
	(assert (y 1))
)

(defrule convertionSouth
	?h1<-(dir south)
=>
	(retract ?h1)
	(assert (y -1))
)

(defrule convertionEast
	?h1<-(dir east)
=>
	(retract ?h1)
	(assert (x 1))
)

(defrule convertionWest
	?h1<-(dir west)
=>
	(retract ?h1)
	(assert (x -1))
)

;-----------------------------------------------------------------------------
;Se limpian las direcciones almacenadas
(defrule cleanDirX
	(declare(salience -9))
	?h<-(x ?)
=>
	(retract ?h)
)

(defrule cleanDirY
	(declare(salience -9))
	?h<-(y ?)
=>
	(retract ?h)
)

;-----------------------------------------------------------------------------
;Cambio de modulo

(defrule exitModule
	(declare(salience -10))
=>
	(return)
)

;=====================================
;Se infieren con los datos obtenidos informacion de las casillas

(defmodule Inferencia (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL))

;Willy se deberia encontrar justo a la derecha del alien
(defrule infer-alien-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla en la que supuestamente se encuentra Willy
	(casilla (x =(- ?x 2))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla dos posiciones a la izquierda en la que ha estado Willy
	?h<-(casilla (x =(- ?x 1))(y ?y)(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;la casilla del medio tiene al alien
	(assert (alien detected (- ?x 1) ?y))
)

;Willy se deberia encontrar justo a la izquierda del alien
(defrule infer-alien-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla en la que supuestamente se encuentra Willy
	(casilla (x =(+ ?x 2))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla dos posiciones a la derecha en la que ha estado Willy
	?h<-(casilla (x =(+ ?x 1))(y ?y)(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;la casilla del medio tiene al alien
	(assert (alien detected (+ ?x 1) ?y))
)

;Willy se deberia encontrar justo encima del alien
(defrule infer-alien-up
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla en la que supuestamente se encuentra Willy
	(casilla (x ?x)(y =(- ?y 2))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla dos posiciones abajo en la que ha estado Willy
	?h<-(casilla (x ?x)(y =(- ?y 1))(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;la casilla del medio tiene al alien
	(assert (alien detected ?x (- ?y 2)))
)

;Willy se deberia encontrar justo debajo del alien
(defrule infer-alien-down
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla en la que supuestamente se encuentra Willy
	(casilla (x ?x)(y =(+ ?y 2))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla dos posiciones arriba en la que ha estado Willy
	?h<-(casilla (x ?x)(y =(+ ?y 1))(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;la casilla del medio tiene al alien
	(assert (alien detected ?x (+ ?y 1)))
)

;detectar al alien desde dos lados en diagonal

(defrule infer-alien-up-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta encima del alien
	(casilla (x =(- ?x 1))(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta a la izquierda del alien
	(casilla (x =(- ?x 1))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;casilla que supuestamente esta en la diagonal superior izquierda del alien
	?h<-(casilla (x ?x)(y =(- ?y 1))(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

(defrule infer-alien-down-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta a la izquierda del alien
	(casilla (x =(+ ?x 1))(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta debajo del alien
	(casilla (x ?x)(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;casilla que supuestamente esta en la diagonal inferior izquierda del alien
	?h<-(casilla (x =(+ ?x 1))(y ?y)(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

(defrule infer-alien-down-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta debajo del alien
	(casilla (x =(+ ?x 1))(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta a la derecha del alien
	(casilla (x =(+ ?x 1))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;casilla que supuestamente esta en la diagonal inferior derecha del alien
	?h<-(casilla (x ?x)(y =(+ ?y 1))(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

(defrule infer-alien-up-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta a la derecha del alien
	(casilla (x =(- ?x 1))(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;casilla que supuestamente esta encima del alien
	(casilla (x ?x)(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;casilla que supuestamente esta en la diagonal superior derecha del alien
	?h<-(casilla (x =(- ?x 1))(y ?y)(visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
) 

;caso en el que la referencia esta a la izquierda del peligro
(defrule detect-alien-1
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que la referencia esta a la derecha del peligro
(defrule detect-alien-2
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que la referencia esta debajo del peligro
(defrule detect-alien-3
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que la referencia esta encima del peligro
(defrule detect-alien-4
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared izquierda y la referencia esta encima del peligro
(defrule detect-alien-5
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared izquierda y la referencia esta debajo del peligro
(defrule detect-alien-6
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la pared derecha y la referencia esta encima del peligro
(defrule detect-alien-7
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared derecha y la referencia esta debajo del peligro
(defrule detect-alien-8
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la pared de arriba y la referencia esta a la izquierda del peligro
(defrule detect-alien-9
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de arriba y la referencia esta a la derecha del peligro
(defrule detect-alien-10
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de abajo y la referencia esta a la derecha del peligro
(defrule detect-alien-11
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de abajo y la referencia esta a la izquierda del peligro
(defrule detect-alien-12
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior izquierda y la referencia esta a la derecha del peligro
(defrule detect-alien-13
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior izquierda y la referencia esta debajo del peligro
(defrule detect-alien-14
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la esquina superior derecha y la referencia esta a la izquierda del peligro
(defrule detect-alien-15
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior derecha y la referencia esta debajo del peligro
(defrule detect-alien-16
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la esquina inferior izquierda y la referencia esta a la derecha del peligro
(defrule detect-alien-17
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla arriba de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina inferior izquierda y la referencia esta encima del peligro
(defrule detect-alien-18
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la esquina inferior derecha y la referencia esta a la izquierda del peligro
(defrule detect-alien-19
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla arriba de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina inferior derecha y la referencia esta encima del peligro
(defrule detect-alien-20
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina superior izquierda y la de debajo esta visitada
(defrule detect-alien-21
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina superior izquierda y la de la derecha esta visitada
(defrule detect-alien-22
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina superior derecha y la de debajo esta visitada
(defrule detect-alien-23
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina superior derecha y la de debajo esta visitada
(defrule detect-alien-24
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina inferior izquierda y la de arriba esta visitada
(defrule detect-alien-25
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina inferior izquierda y la de la derecha esta visitada
(defrule detect-alien-26
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;caso en el que el pull se detecta en la esquina inferior derecha y la de arriba esta visitada
(defrule detect-alien-27
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;caso en el que el noise se detecta en la esquina inferior derecha y la de la izquierda esta visitada
(defrule detect-alien-28
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;==============================================================================================================================================
;Una vez detectado el alien, podemos dispararle


;inferencia del agujero negro

;caso en el que la referencia esta a la izquierda del peligro
(defrule detect-hole-1
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que la referencia esta a la derecha del peligro
(defrule detect-hole-2
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que la referencia esta debajo del peligro
(defrule detect-hole-3
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que la referencia esta encima del peligro
(defrule detect-hole-4
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared izquierda y la referencia esta encima del peligro
(defrule detect-hole-5
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared izquierda y la referencia esta debajo del peligro
(defrule detect-hole-6
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la pared derecha y la referencia esta encima del peligro
(defrule detect-hole-7
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la pared derecha y la referencia esta debajo del peligro
(defrule detect-hole-8
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la pared de arriba y la referencia esta a la izquierda del peligro
(defrule detect-hole-9
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de arriba y la referencia esta a la derecha del peligro
(defrule detect-hole-10
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de abajo y la referencia esta a la derecha del peligro
(defrule detect-hole-11
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la pared de abajo y la referencia esta a la izquierda del peligro
(defrule detect-hole-12
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla encima de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior izquierda y la referencia esta a la derecha del peligro
(defrule detect-hole-13
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior izquierda y la referencia esta debajo del peligro
(defrule detect-hole-14
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la esquina superior derecha y la referencia esta a la izquierda del peligro
(defrule detect-hole-15
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina superior derecha y la referencia esta debajo del peligro
(defrule detect-hole-16
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que el peligro esta en la esquina inferior izquierda y la referencia esta a la derecha del peligro
(defrule detect-hole-17
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla arriba de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina inferior izquierda y la referencia esta encima del peligro
(defrule detect-hole-18
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el peligro esta en la esquina inferior derecha y la referencia esta a la izquierda del peligro
(defrule detect-hole-19
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla arriba de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el peligro esta en la esquina inferior derecha y la referencia esta encima del peligro
(defrule detect-hole-20
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ; casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ; casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina superior izquierda y la de debajo esta visitada
(defrule detect-hole-21
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina superior izquierda y la de la derecha esta visitada
(defrule detect-hole-22
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina superior derecha y la de debajo esta visitada
(defrule detect-hole-23
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina superior derecha y la de debajo esta visitada
(defrule detect-hole-24
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (- ?y 1)))
)

;caso en el que el pull se detecta en la esquina inferior izquierda y la de arriba esta visitada
(defrule detect-hole-25
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (+ ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina inferior izquierda y la de la derecha esta visitada
(defrule detect-hole-26
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;caso en el que el pull se detecta en la esquina inferior derecha y la de arriba esta visitada
(defrule detect-hole-27
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected (- ?x 1) ?y))
)

;caso en el que el pull se detecta en la esquina inferior derecha y la de la izquierda esta visitada
(defrule detect-hole-28
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0)) ;casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)) ;casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (hole 1) (danger 1))
	(assert (hole detected ?x (+ ?y 1)))
)

;es facil poner como seguras las casillas que podrian haber contenido un alien, porque solo hay
;pero con los agujeros no se puede tan facilmente, habria que pensar si merece la pena poner casillas como seguras 
;o solo tener controladas las casillas donde haya agujeros (piensa en el caso en el que haya dos agujeros juntos y detecto uno 
;de ellos, no puedo poner las casillas a su alrededor como seguras porque en una hay un puto agujero xddddd
;lo mejor creo yo es tenerlos controlados donde estan y evitarlos a toda costa

;(defrule discard-hole
;	
;)

;(defrule discard-alien
;
;)

;Cambio de modulo
(defrule exitModule
	(declare(salience -10))
=>
	(return)
)

;-----------------------------------------------------------------------------
;Dispara cuando sabe donde esta el alien
(defrule shootNorth
	(hasLaser)
	?h<-(alien detected ?x ?y)
	(willy (x ?x) (y ?z))
	(test (> ?y ?z))
=>
	(fireLaser north)
	(retract ?h)
	(assert (deadAlien))
)

(defrule shootEast
	(hasLaser)
	?h<-(alien detected ?x ?y)
	(willy (x ?z) (y ?y))
	(test (> ?x ?z))
=>
	(fireLaser east)
	(retract ?h)
	(assert (deadAlien))
)

(defrule shootWest
	(hasLaser)
	?h<-(alien detected ?x ?y)
	(willy (x ?z) (y ?y))
	(test (< ?x ?z))
=>
	(fireLaser west)
	(retract ?h)
	(assert (deadAlien))
)

(defrule shootSouth
	(hasLaser)
	?h<-(alien detected ?x ?y)
	(willy (x ?x) (y ?z))
	(test (< ?y ?z))
=>
	(fireLaser south)
	;(retract ?h)
	(assert (deadAlien))
)

;=========================================
;Willy se desplaza

(defmodule Movimiento (import MAIN deftemplate ?ALL) (import myMAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL))

;-----------------------------------------------------------------------------
;Inicializa el vector de movimientos

(defrule init
	(not (moVector $?))
=>
	(assert (moVector))
)

;-----------------------------------------------------------------------------
;Willy se movera hacia casillas seguras y no visitadas con prioridad max

(defrule moveNorth
	(declare (salience 2))
	?h1<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0))
	?h2<-(moVector $?all)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly north)
	(assert (moVector $?all north))
	(assert(willy (x ?x) (y (+ ?y 1))))
	(assert (movido))
)

(defrule moveSouth
	(declare (salience 2))
	?h1<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0))
	?h2<-(moVector $?all)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly south)
	(assert (moVector $?all south))
	(assert(willy (x ?x) (y (- ?y 1))))
	(assert (movido))
)

(defrule moveEast
	(declare (salience 2))
	?h1<-(willy (x ?x) (y ?y))
	(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0))
	?h2<-(moVector $?all)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly east)
	(assert (moVector $?all east))
	(assert(willy (x (+ ?x 1)) (y ?y)))
	(assert (movido))
)

(defrule moveWest
	(declare (salience 2))
	?h1<-(willy (x ?x) (y ?y))
	(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 1) (alien 0) (hole 0) (pull ?) (noise ?) (danger 0))
	?h2<-(moVector $?all)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly west)
	(assert (moVector $?all west))
	(assert(willy (x (- ?x 1)) (y ?y)))
	(assert (movido))
)

;-----------------------------------------------------------------------------
;Willy se movera hacia atras por donde a venido si no sabe por donde avanzar

(defrule moveBackSouth
	?h1<-(willy (x ?x) (y ?y))
	?h2<-(moVector $?all north)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly south)
	(assert(willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all))
	(assert (movido))
)

(defrule moveBackNorth
	?h1<-(willy (x ?x) (y ?y))
	?h2<-(moVector $?all south)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly north)
	(assert(willy (x ?x) (y (+ ?y 1))))
	(assert (moVector $?all))
	(assert (movido))
)

(defrule moveBackEast
	?h1<-(willy (x ?x) (y ?y))
	?h2<-(moVector $?all west)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly east)
	(assert(willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all))
	(assert (movido))
)

(defrule moveBackWest
	?h1<-(willy (x ?x) (y ?y))
	?h2<-(moVector $?all east)
	(not(movido))
=>
	(retract ?h1)
	(retract ?h2)
	(moveWilly west)
	(assert(willy (x (- ?x 1)) (y ?y)))
	(assert (moVector $?all))
	(assert (movido))
)

;-----------------------------------------------------------------------------
;Si no hay mas casillas seguros o no visitadas disponibles se activa la señal de parada

(defrule stop
	(declare(salience -9))
	?h<-(STOP (state false))
	(or (not(movido)) (not(casilla (x ?) (y ?) (visited 0) (safe 1) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))))
=>
	(retract ?h)
	(assert (STOP (state true)))
)

;-----------------------------------------------------------------------------
;Cambio de modulo
(defrule exitModule
	(declare(salience -10))
	?h1<-(movido)
=>
	(retract ?h1)
	(return)
)
