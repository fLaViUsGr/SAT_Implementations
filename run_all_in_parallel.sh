#!/bin/bash

parallel -u ::: 'python3.12 Resolution_SAT_Implementation.py' 'python3.12 DavisPutnam_SAT_Implementation.py' 'python3.12 DavisPutnamLogemannLoveland_SAT_Implementation.py'
