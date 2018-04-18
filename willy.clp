;*****************************************
; Autores:
; Historial de cambios:
;  - Fecha: mejoras/cambios
;*****************************************

(defrule MAIN::passToPercepcion
	=>
	(focus Percepcion))


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
	(assert (casilla (x 0)(y 0) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 0) (danger 0)))
	(assert (willy (x 0) (y 0)))
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


;Cambio de modulo
(defrule passToInferencia
	(declare(salience -10))
=>
	(focus Inferencia))

;=====================================
;Se infieren con los datos obtenidos informacion de las casillas

(defmodule Inferencia (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL))

;Cambio de modulo
(defrule passToMovimiento
	(declare(salience -10))
=>
	(focus Movimiento))



;=========================================
;Willy se desplaza

(defmodule Movimiento (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (import Percepcion deftemplate ?ALL))

;Cambio de modulo
(defrule passToPercepcion
	(declare(salience -10))
=>
	(focus Percepcion))
