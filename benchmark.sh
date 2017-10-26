#!/bin/sh
#
# Used for running all benchmarks, since cargo bench alone doesn't
# accommodate our memory benchmarks.

set -eu

die() {
    exec 1>&2
    cat
    exit 1
}

# Validate the machine is in a safe state for benchmarking
if [ -d /sys/devices/system/cpu/cpufreq/ ]; then
    if grep -qv performance /sys/devices/system/cpu/cpufreq/policy*/scaling_governor; then
        die <<EOF
Please set your CPU scaling governor to performance before trying to
benchmark things.  This might do the trick:
  sudo cpupower -c all frequency-set -g performance &&
  sudo cpupower -c all set -b 0
EOF
    fi
fi
# I forget how to check this on other operating systems.
# Contributions welcome.

# There are other things to check, like the NMI watchdog, and we
# should consider pinning affinity, but I'll avoid being too much of a
# nag.

# Write minimal useful identifying info: CPU, load, et cetera.
echo ==============
hostname
uptime
uname -a
sed -n 's/model name.*: \(.*\)/\1/p' /proc/cpuinfo | sort | uniq -c
grep flags /proc/cpuinfo | sort -u
echo ==============
echo

cargo bench

# Run memory benches
# Depends on GNU time and shuf; sorry.
cargo build --release --examples
echo Memory usage per n elements:
echo as sets:
for test in $(shuf -e qp_trie_set fixie_trie_set btree_set hash_set); do
    echo "$test: "
    for n in 10000 100000 1000000 10000000; do
        /usr/bin/time -f "  $n: %M kB" ./target/release/examples/benchmark-memory "$test" "$n"
    done
done

echo as maps:
for test in $(shuf -e qp_trie fixie_trie btree_map hash_map); do
    echo "$test: "
    for n in 10000 100000 1000000 10000000; do
        /usr/bin/time -f "  $n: %M kB" ./target/release/examples/benchmark-memory "$test" "$n"
    done
done
