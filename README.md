# angle-sc

[![crates.io](https://img.shields.io/crates/v/angle-sc.svg)](https://crates.io/crates/angle-sc)
[![docs.io](https://docs.rs/angle-sc/badge.svg)](https://docs.rs/angle-sc/)
[![License](https://img.shields.io/badge/License-MIT-blue)](https://opensource.org/license/mit/)
[![Rust](https://github.com/kenba/angle-sc-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/kenba/angle-sc-rs/actions)
[![codecov](https://codecov.io/gh/kenba/angle-sc-rs/graph/badge.svg?token=6DTOY9Y4BT)](https://codecov.io/gh/kenba/angle-sc-rs)

An angle represented by its sine and cosine.

The cosine and sine of angle *θ* can be viewed as *x* and *y* coordinates,
with *θ* measured anti-clockwise from the *x* axis.  
They form a [unit circle](https://en.wikipedia.org/wiki/Unit_circle), see *Figure 1*.

![Unit circle](https://upload.wikimedia.org/wikipedia/commons/thumb/7/72/Sinus_und_Kosinus_am_Einheitskreis_1.svg/250px-Sinus_und_Kosinus_am_Einheitskreis_1.svg.png)  
*Figure 1 Unit circle formed by sin *θ* and cos *θ**

## Design

![Angle Class Diagram](docs/images/angle_class_diagram.svg)  
*Figure 2 Angle Class Diagram*

The `Angle` on the `opposite` side of the unit circle is calculated by simply
negating the sin and cos of `Angle`.  
`Angle` addition and subtraction are performed using
[angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).  
`Angle` `double` uses the [double-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Double-angle_formulae)
and `half` uses the [half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae).  
The `Angle` `<` operator compares whether an `Angle` is clockwise of the other
`Angle` on the unit circle.

The `sin` and `cos` fields of `Angle` are `UnitNegRange`s:,
a [newtype](https://rust-unofficial.github.io/patterns/patterns/behavioural/newtype.html)
with values in the range -1.0 to +1.0 inclusive.  
The `Degrees` and `Radians` newtypes are used to convert to and from `Angle`s.  
The `Validate` trait is used to check that `Angle`s and `UnitNegRange`s are valid.

The library is declared [no_std](https://docs.rust-embedded.org/book/intro/no-std.html)
so it can be used in embedded applications.

## Contribution

If you want to contribute through code or documentation, the [Contributing](CONTRIBUTING.md) guide is the best place to start. If you have any questions, please feel free to ask.
Just please abide by our [Code of Conduct](CODE_OF_CONDUCT.md).

## License

`angle-rs` is provided under a MIT license, see [LICENSE](LICENSE).
