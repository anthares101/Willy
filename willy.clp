;*****************************************
; Autores: Ángel Heredia Pérez y Sergio Gómez Morales
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

(defrule passToInitialRule
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
	(slot visited)						;Casilla visitada
	(slot safe)							;La casilla es totalmente segura
	(slot alien)						;Hay alien en la casilla
	(slot hole)							;Hay agujero en la casilla
	(slot pull)							;Se percibe empuje
	(slot noise)						;Se percibe sonido
	(slot danger)						;La casilla tiene un peligro seguro sin especificar cual
)
(deftemplate willy					;Informacion de la informacion actual de willy
	(slot x)
	(slot y)
)

;Crea la primera casilla del mapa (donde aparece Willy)

(defrule firstState
	(not (casilla (x ?)(y ?) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
=>
	(assert (casilla (x 0) (y 0) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 0) (danger 0)))
	(assert (willy (x 0) (y 0)))
)

;Crea la casilla en la que Willy se encuentra si no existia

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
;Este conjunto de reglas infiere si en una casilla se esta seguro que no hay un agujero o un alien y en caso de que no haya ninguno pues será segura

(defrule lookForAlienX
	(declare (salience -2))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 0) (danger ?))
	(x ?mX)
	(casilla (x =(+ ?mX ?x)) (y ?y) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(assert (notAlien (+ ?mX ?x) ?y))
)

(defrule lookForAlienY
	(declare (salience -2))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 0) (danger ?))
	(y ?mY)
	(casilla (x ?x) (y =(+ ?mY ?y)) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(assert (notAlien ?x (+ ?mY ?y)))
)

(defrule lookForHoleX
	(declare (salience -2))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull 0) (noise ?) (danger ?))
	(x ?mX)
	(casilla (x =(+ ?mX ?x)) (y ?y) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(assert (notHole (+ ?mX ?x) ?y))
)

(defrule lookForHoleY
	(declare (salience -2))
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull 0) (noise ?) (danger ?))
	(y ?mY)
	(casilla (x ?x) (y =(+ ?mY ?y)) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
=>
	(assert (notHole ?x (+ ?mY ?y)))
)

(defrule safeState
	?h1<-(casilla (x ?x) (y ?y) (visited ?v) (safe 0) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d))
	?h2<-(notHole ?x ?y)
	?h3<-(notAlien ?x ?y)
=>
	(retract ?h1 ?h2 ?h3)
	(assert (casilla (x ?x) (y ?y) (visited ?v) (safe 1) (alien ?a) (hole ?h) (pull ?p) (noise ?n) (danger ?d)))
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

(defmodule Inferencia (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL) (export deftemplate ?ALL))

;Willy se deberia encontrar justo a la derecha del alien

(defrule infer-alien-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla en la que supuestamente se encuentra Willy
	(casilla (x =(- ?x 2))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla dos posiciones a la izquierda en la que ha estado Willy
	?h<-(casilla (x =(- ?x 1))(y ?y)(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;La casilla del medio tiene al alien
	(assert (alien detected (- ?x 1) ?y))
)

;Willy se deberia encontrar justo a la izquierda del alien

(defrule infer-alien-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla en la que supuestamente se encuentra Willy
	(casilla (x =(+ ?x 2))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla dos posiciones a la derecha en la que ha estado Willy
	?h<-(casilla (x =(+ ?x 1))(y ?y)(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;La casilla del medio tiene al alien
	(assert (alien detected (+ ?x 1) ?y))
)

;Willy se deberia encontrar justo encima del alien

(defrule infer-alien-up
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla en la que supuestamente se encuentra Willy
	(casilla (x ?x)(y =(- ?y 2))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla dos posiciones abajo en la que ha estado Willy
	?h<-(casilla (x ?x)(y =(- ?y 1))(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;La casilla del medio tiene al alien
	(assert (alien detected ?x (- ?y 2)))
)

;Willy se deberia encontrar justo debajo del alien

(defrule infer-alien-down
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla en la que supuestamente se encuentra Willy
	(casilla (x ?x)(y =(+ ?y 2))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla dos posiciones arriba en la que ha estado Willy
	?h<-(casilla (x ?x)(y =(+ ?y 1))(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1)) ;La casilla del medio tiene al alien
	(assert (alien detected ?x (+ ?y 1)))
)

;-----------------------------------------------------------------------------
;Detectar al alien desde dos lados en diagonal

(defrule infer-alien-up-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta encima del alien
	(casilla (x =(- ?x 1))(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta a la izquierda del alien
	(casilla (x =(- ?x 1))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que supuestamente esta en la diagonal superior izquierda del alien
	?h<-(casilla (x ?x)(y =(- ?y 1))(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

(defrule infer-alien-down-left
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta a la izquierda del alien
	(casilla (x =(+ ?x 1))(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta debajo del alien
	(casilla (x ?x)(y =(- ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que supuestamente esta en la diagonal inferior izquierda del alien
	?h<-(casilla (x =(+ ?x 1))(y ?y)(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

(defrule infer-alien-down-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta debajo del alien
	(casilla (x =(+ ?x 1))(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta a la derecha del alien
	(casilla (x =(+ ?x 1))(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que supuestamente esta en la diagonal inferior derecha del alien
	?h<-(casilla (x ?x)(y =(+ ?y 1))(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

(defrule infer-alien-up-right
	(casilla (x ?x)(y ?y)(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta a la derecha del alien
	(casilla (x =(- ?x 1))(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0)) ;Casilla que supuestamente esta encima del alien
	(casilla (x ?x)(y =(+ ?y 1))(visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que supuestamente esta en la diagonal superior derecha del alien
	?h<-(casilla (x =(- ?x 1))(y ?y)(visited 0) (safe ?) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)
 
;-----------------------------------------------------------------------------
;Caso en el que la referencia esta a la izquierda del peligro

(defrule detect-alien-1
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;Caso en el que la referencia esta a la derecha del peligro
(defrule detect-alien-2
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla encima de la referencia
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;Caso en el que la referencia esta debajo del peligro

(defrule detect-alien-3
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;Caso en el que la referencia esta encima del peligro

(defrule detect-alien-4
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la derecha de la referencia
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;-----------------------------------------------------------------------------
;Caso en el que el peligro esta en la pared izquierda y la referencia esta encima del peligro

(defrule detect-alien-5
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;Caso en el que el peligro esta en la pared izquierda y la referencia esta debajo del peligro

(defrule detect-alien-6
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la derecha de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;Caso en el que el peligro esta en la pared derecha y la referencia esta encima del peligro

(defrule detect-alien-7
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;Caso en el que el peligro esta en la pared derecha y la referencia esta debajo del peligro

(defrule detect-alien-8
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla a la izquierda de la referencia
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;Caso en el que el peligro esta en la pared de arriba y la referencia esta a la izquierda del peligro

(defrule detect-alien-9
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla debajo de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;Caso en el que el peligro esta en la pared de arriba y la referencia esta a la derecha del peligro

(defrule detect-alien-10
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla debajo de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;Caso en el que el peligro esta en la pared de abajo y la referencia esta a la derecha del peligro

(defrule detect-alien-11
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla encima de la referencia
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;Caso en el que el peligro esta en la pared de abajo y la referencia esta a la izquierda del peligro

(defrule detect-alien-12
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla opuesta al peligro
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla encima de la referencia
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=> 
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;-----------------------------------------------------------------------------
;Caso en el que el noise se detecta en la esquina superior izquierda y la de debajo es safe

(defrule detect-alien-13
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;Caso en el que el noise se detecta en la esquina superior izquierda y la de la derecha es safe

(defrule detect-alien-14
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;Caso en el que el noise se detecta en la esquina superior derecha y la de debajo es safe

(defrule detect-alien-15
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;Caso en el que el noise se detecta en la esquina superior derecha y la de debajo es safe

(defrule detect-alien-16
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (- ?y 1)))
)

;Caso en el que el noise se detecta en la esquina inferior izquierda y la de arriba es safe

(defrule detect-alien-17
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (+ ?x 1) ?y))
)

;Caso en el que el noise se detecta en la esquina inferior izquierda y la de la derecha es safe

(defrule detect-alien-18
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;Caso en el que el noise se detecta en la esquina inferior derecha y la de arriba es safe

(defrule detect-alien-19
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected (- ?x 1) ?y))
)

;Caso en el que el noise se detecta en la esquina inferior derecha y la de la izquierda es safe
(defrule detect-alien-20
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull ?) (noise 1) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe 1) (alien 0) (hole 0) (pull ?) (noise 0) (danger 0)) ;Casilla que no es la del peligro
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited 0) (safe 0) (alien 0) (hole ?) (pull ?) (noise ?) (danger ?)) ;Casilla del peligro
	(not (casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	(not (casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	=>
	(modify ?h (safe 0) (alien 1) (danger 1))
	(assert (alien detected ?x (+ ?y 1)))
)

;-----------------------------------------------------------------------------
;Es facil poner como seguras las casillas que podrian haber contenido un alien, porque solo hay
;pero con los agujeros no se puede tan facilmente, habria que pensar si merece la pena poner casillas como seguras 
;o solo tener controladas las casillas donde haya agujeros (piensa en el caso en el que haya dos agujeros juntos y detecto uno 
;de ellos, no puedo poner las casillas a su alrededor como seguras, lo mejor es tener controlado donde estan y evitarlos

(defrule discard-alien-1
	(declare (salience 2))
	(deadAlien)
	(alien detected ?x ?y)
	?h<-(casilla (x ?x) (y ?y) (visited ?) (safe 0) (alien 1) (hole ?) (pull ?) (noise ?) (danger 1))
	=>
	(modify ?h (safe 1) (alien 0) (danger 0))
	
)

(defrule discard-alien-2
	(declare (salience 2))
	(deadAlien)
	(alien detected ?x ?y)
	?h<-(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 1) (danger ?))
	=>
	(modify ?h (noise 0)) 
)

(defrule discard-alien-3
	(declare (salience 2))
	(deadAlien)
	(alien detected ?x ?y)
	?h<-(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 1) (danger ?))
	=>
	(modify ?h (noise 0))
)

(defrule discard-alien-4
	(declare (salience 2))
	(deadAlien)
	(alien detected ?x ?y)
	?h<-(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 1) (danger ?))
	=>
	(modify ?h (noise 0))
)

(defrule discard-alien-5
	(declare (salience 2))
	(deadAlien)
	(alien detected ?x ?y)
	?h<-(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise 1) (danger ?))
	=>
	(modify ?h (noise 0))
)

;-----------------------------------------------------------------------------
;Dispara cuando sabe donde esta el alien

(defrule shootNorth
	(hasLaser)
	(alien detected ?x ?y)
	(willy (x ?x) (y ?z))
	(test (> ?y ?z))
=>
	(fireLaser north)
	(assert (deadAlien))
)

(defrule shootEast
	(hasLaser)
	(alien detected ?x ?y)
	(willy (x ?z) (y ?y))
	(test (> ?x ?z))
=>
	(fireLaser east)
	(assert (deadAlien))
)

(defrule shootWest
	(hasLaser)
	(alien detected ?x ?y)
	(willy (x ?z) (y ?y))
	(test (< ?x ?z))
=>
	(fireLaser west)
	(assert (deadAlien))
)

(defrule shootSouth
	(hasLaser)
	(alien detected ?x ?y)
	(willy (x ?x) (y ?z))
	(test (< ?y ?z))
=>
	(fireLaser south)
	(assert (deadAlien))
)

;-----------------------------------------------------------------------------
;Cambio de modulo

(defrule exitModule
	(declare(salience -10))
=>
	(return)
)

;=========================================
;Willy se desplaza

(defmodule Movimiento (import MAIN deftemplate ?ALL) (import myMAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL) (import Inferencia deftemplate ?ALL))

;-----------------------------------------------------------------------------
;Inicializa el vector de movimientos

(defrule init
	(not (moVector $?))
	(not (numMov ?))
=>
	(assert (moVector))
	(assert (numMov 1))
)

;Willy detecta un Noise y se activa su instinto asesino siempre y cuando en dicha casilla no haya Pull y no haya abortado anteriormente el algoritmo.
;Este conjunto de reglas tratan de inferir con prioridad maxima la posicion del alien para matarlo (siempre y cuando no se ponga en peligro a Willy)
;realizando la forma de una T que se formará en la dirección contraria a la que se llego a la casilla con el Noise, formandose completa o solo una parte
;en función de si se encuentra o no cerca de alguna pared. El movimiento realizado en conjunto con el modulo de inferencia provoca la deteccion de la posicion
;del alien y su consecuente ejecucion.

;Cuando el ultimo movimiento que hizo fue al norte
(defrule T-algorithm-1-north
	(declare (salience 8))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 1) (danger 0)) ;Casilla en la que se detecta Noise
	?h1<-(moVector $?all north)
	(not(movido))
	(not (deadAlien))
	(not (assassin instinct vertical))
	(not (abort))
=>
	(moveWilly south)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all north south))
	(assert (movido))
	(assert (assassin instinct vertical))
)

(defrule T-algorithm-2-north-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all south)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (abort))
=>
	(moveWilly west)
	(retract ?h ?h1)
	(assert (willy (x (- ?x 1)) (y ?y)))
	(assert (moVector $?all south west))
	(assert (movido))
)

(defrule T-algorithm-2-north-not-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	?h1<-(moVector $?all south)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (abort))
=>
	(moveWilly east)
	(retract ?h ?h1)
	(assert (willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all south east))
	(assert (movido))
	(assert (paso4))
)

;Cuando el ultimo movimiento fue hacia el sur
(defrule T-algorithm-1-south
	(declare (salience 8))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 1) (danger 0)) ;Casilla en la que se detecta Noise
	?h1<-(moVector $?all south)
	(not(movido))
	(not (deadAlien))
	(not (assassin instinct vertical))
	(not (abort))
=>
	(moveWilly north)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (+ ?y 1))))
	(assert (moVector $?all south north))
	(assert (movido))
	(assert (assassin instinct vertical))
)

(defrule T-algorithm-2-south-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all north)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (abort))
=>
	(moveWilly west)
	(retract ?h ?h1)
	(assert (willy (x (- ?x 1)) (y ?y)))
	(assert (moVector $?all north west))
	(assert (movido))
)

(defrule T-algorithm-2-south-not-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(not (casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	?h1<-(moVector $?all north)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (abort))
=>
	(moveWilly east)
	(retract ?h ?h1)
	(assert (willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all north east))
	(assert (movido))
	(assert (paso4))
)

;Cuando el ultimo movimiento fue hacia el oeste
(defrule T-algorithm-1-west
	(declare (salience 8))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 1) (danger 0)) ;Casilla en la que se detecta Noise
	?h1<-(moVector $?all west)
	(not(movido))
	(not (deadAlien))
	(not (assassin instinct horinzontal))
	(not (abort))
=>
	(moveWilly east)
	(retract ?h ?h1)
	(assert (willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all west east))
	(assert (movido))
	(assert (assassin instinct horizontal))
)

(defrule T-algorithm-2-west-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all east)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (abort))
=>
	(moveWilly north)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (+ ?y 1))))
	(assert (moVector $?all east north))
	(assert (movido))
)

(defrule T-algorithm-2-west-not-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	?h1<-(moVector $?all east)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (abort))
=>
	(moveWilly south)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all east south))
	(assert (movido))
	(assert (paso4))
)

;Cuando el ultimo movimiento fue hacia el este
(defrule T-algorithm-1-east
	(declare (salience 8))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 1) (danger 0)) ;Casilla en la que se detecta Noise
	?h1<-(moVector $?all east)
	(not(movido))
	(not (deadAlien))
	(not (assassin instinct horinzontal))
	(not (abort))
=>
	(moveWilly west)
	(retract ?h ?h1)
	(assert (willy (x (- ?x 1)) (y ?y)))
	(assert (moVector $?all east west))
	(assert (movido))
	(assert (assassin instinct horizontal))
)

(defrule T-algorithm-2-east-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all west)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (abort))
=>
	(moveWilly north)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (+ ?y 1))))
	(assert (moVector $?all west north))
	(assert (movido))
)

(defrule T-algorithm-2-east-not-happy-path
	(declare (salience 7))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(not (casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?)))
	?h1<-(moVector $?all west)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (abort))
=>
	(moveWilly south)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all west south))
	(assert (movido))
	(assert (paso4))
)

;Movimientos verticales

(defrule T-algorithm-vertical-1
	(declare (salience 6))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all north)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (abort))
=>
	(moveWilly south)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all north south))
	(assert (movido))
	(assert (paso4))
)

(defrule T-algorithm-vertical-2
	(declare (salience 5))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x ?x) (y =(- ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all south)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(not (done))
	(not (abort))
	?h2<-(paso4)
=>
	(moveWilly south)
	(retract ?h ?h1 ?h2)
	(assert (willy (x ?x) (y (- ?y 1))))
	(assert (moVector $?all south south))
	(assert (movido))
	(assert (done))
)

(defrule T-algorithm-vertical-3
	(declare (salience 4))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x ?x) (y =(+ ?y 1)) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all south)
	(not (movido))
	(not (deadAlien))
	(assassin instinct horizontal)
	(done)
	(not (abort))
=>
	(moveWilly north)
	(retract ?h ?h1)
	(assert (willy (x ?x) (y (+ ?y 1))))
	(assert (moVector $?all south north))
	(assert (movido))
)

;Movimientos horizontales

(defrule T-algorithm-horizontal-1
	(declare (salience 6))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all west)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (abort))
=>
	(moveWilly east)
	(retract ?h ?h1)
	(assert (willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all west east))
	(assert (movido))
	(assert (paso4))
)

(defrule T-algorithm-horizontal-2
	(declare (salience 5))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x =(+ ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all east)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(not (done))
	(not (abort))
	?h2<-(paso4)
=>
	(moveWilly east)
	(retract ?h ?h1 ?h2)
	(assert (willy (x (+ ?x 1)) (y ?y)))
	(assert (moVector $?all east east))
	(assert (movido))
	(assert (done))
)

(defrule T-algorithm-horizontal-3
	(declare (salience 4))
	?h<-(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise ?) (danger 0))
	(casilla (x =(- ?x 1)) (y ?y) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))
	?h1<-(moVector $?all east)
	(not (movido))
	(not (deadAlien))
	(assassin instinct vertical)
	(done)
	(not (abort))
=>
	(moveWilly west)
	(retract ?h ?h1)
	(assert (willy (x (- ?x 1)) (y ?y)))
	(assert (moVector $?all east west))
	(assert (movido))
)

(defrule calm-down
	(willy (x ?x) (y ?y))
	(casilla (x ?x) (y ?y) (visited 1) (safe 1) (alien 0) (hole 0) (pull 1) (noise ?) (danger 0))
	?h<-(assassin instinct ?)
=>
	(retract ?h)
	(assert (abort))
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
;Willy se movera hacia atras por donde ha venido si no sabe por donde avanzar

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
;Si no hay mas casillas seguras o no visitadas disponibles se activa la señal de parada, tambien si no se ha podido mover o bien para no morir a los 1000 movimientos

(defrule stop
	(declare(salience -9))
	?h<-(STOP (state false))
	(or (not(movido)) (not(casilla (x ?) (y ?) (visited 0) (safe 1) (alien ?) (hole ?) (pull ?) (noise ?) (danger ?))) (numMov 998))
=>
	(retract ?h)
	(assert (STOP (state true)))
)

;-----------------------------------------------------------------------------
;Cambio de modulo

(defrule exitModule
	(declare(salience -10))
	?h1<-(numMov ?num)
	?h2<-(movido)
=>
	(retract ?h1 ?h2)
	(assert (numMov (+ ?num 1)))
	(return)
)
