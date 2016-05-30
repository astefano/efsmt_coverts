#!/bin/bash
for i in `seq 9 16`;
do
	sed "s/_0/_$i/g" train0.imi > train$i.imi
done
