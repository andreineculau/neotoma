all: compile

compile:
	@ rebar compile

tests:
	@ rebar eunit

clean:
	@ rebar clean

dialyze: compile
	@ rebar dialyze

bootstrap: compile
	@ erl -pz ebin -b start_sasl -noshell -s init stop -s neotoma bootstrap
	@ rebar compile

pegerl: compile
	@ erl -pz ebin -b start_sasl -noshell -s init stop -s neotoma bootstrap_pegerl
	@ rebar compile

escript:
	@ rebar escriptize
