An implementation of "fixie tries", inspired by Tony Finch's
[qp-tries] but for fixed-length keys, storing the key implicitly in
the trie where possible.

*This needs benchmarks before you should even consider using it.*

There are countless trie variants, so although I'm giving this one a
new name, it probably already exists in some form.

This is x86_64-specific, because we stuff the branch bitmap in the
upper 16 bits of a pointer; pointers on this platform are actually
48-bit, so no harm done, but this doesn't necessarily hold on other
platforms.  And there wouldn't be enough room for the bitmap if
pointers were 32-bit.

(The mask for pointers is `0x0000_ffff_ffff_fffe`.)

Part of my interest in doing this was to see if it was possible to
write this kind of stuff in Rust, and it seems to be possible and
mostly pleasant.

This implementation is mostly an experiment; in particular, the
current approach is unfriendly to the allocator, making a lot of tiny
allocations.  Slab allocation or similar would probably make sense.

It might be nice to do something like direct pointing from [poptries]
on top, where the first _n_ bits are covered by a 2ⁿ array of tries.

[qp-tries]: http://dotat.at/prog/qp/
[poptries]: http://conferences.sigcomm.org/sigcomm/2015/pdf/papers/p57.pdf
