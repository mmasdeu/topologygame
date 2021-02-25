#!/bin/sh
~/.local/bin/make-lean-game
scp -Cr html/* math:www/topologygame/
