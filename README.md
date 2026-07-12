# IntensionalSetoids

### [github.com/amp12/IntensionalSetoids](https://github.com/amp12/IntensionalSetoids)

We give a new notion of displayed setoid (family of setoids) in intensional type theory. It is used to give a semantics of extensional type theory with universes (ETU) within Agda with
options `--safe` and `--without-K`, used as a machine-checkable formalization of intentional type theory augmented with a universe closed under inductive-recursive definitions (ITU). The syntax of ETU is defined in safe Agda in a traditional extrinsic form, using an Agda library [WSLN](https://amp12.github.io/WSLN/html/WSLN.html) for well-scoped locally nameless representation of its expressions. Giving its semantics in the ITU setoid model is complicated by the very limited means of expression afforded by ITU. As a corollary we obtain a proof of the consistency of ETU within ITU.

### [Browsable code](https://amp12.github.io/IntensionalSetoids/html/README.html)

Checked with Agda version 2.8.0 using options

  `--safe`
  `--without-K`
  `--no-postfix-projections`
  
  
