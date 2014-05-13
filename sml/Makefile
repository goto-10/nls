# Suppress pointless polyEqual warning.
SMLFLAGS=-Ccontrol.poly-eq-warn=false

FILES=         \
eval.sml       \
neutrino.sml   \
syntax.sml     \
test.sml       \
utils.sml      \
value.sml

main:	$(FILES)
	sml $(SMLFLAGS) test.sml
