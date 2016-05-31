#!/bin/bash
for i in `seq 17 32`;
do
	sed "s/_0/_$i/g" rod0.imi > rod$i.imi
done
