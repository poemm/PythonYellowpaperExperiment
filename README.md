
Setup.
```
pip install pysha3
pip install coincurve

tar -xvzf blocks00000000.tar.gz 	# first 60,000 blocks
tar -xvzf uncles_00000000.tar.gz	# uncles for first 60,000 blocks
```

Execute blocks starting from genesis. Currently executes up to block `49018`, need to fix bugs to go further.
```
python3 main.py
```


