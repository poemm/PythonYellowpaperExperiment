
Setup.
```
pip install pysha3
pip install coincurve
```

Execute blocks starting from genesis. Currently executes up to block `49018`, need to fix bugs to go further.
```
tar -xvzf blocks00000000.tar.gz 	# first 60,000 blocks
tar -xvzf uncles_00000000.tar.gz	# uncles for first 60,000 blocks

python3 main.py
```

Execute spec tests. This should pass all VM tests. Need more work to pass blockchain tests and state tests.
```
git clone https://github.com/ethereum/tests	# downloads like 300MB
cd tests
git checkout 66a55cd42f63845e34767504d0a7a62b452a7e7a	# the November 2020 version of this repo where VMTests passed
cd ..

python3 test.py
```

