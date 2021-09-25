/^[^:]+:[0-9]+:[0-9]+:\s+(error|warning):.*/{
:loop
N
s/\n(.+)/%0A\1/
tloop
}
