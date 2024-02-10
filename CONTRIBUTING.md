# How to contribute

First off, I'm really glad you're reading this, because we need volunteer developers to help improve this project and make it more useful to other developers.

The following is a set of guidelines for contributing to this repository  which are hosted on GitHub. These are mostly guidelines, not rules. Use your best judgment, and feel free to propose changes to this document in a pull request.

## Where do I go from here?

If you've noticed a bug or have a feature request then please raise a [new issue](https://github.com/kenba/angle-sc-rs/issues/new).
It's generally best to check the [issues](https://github.com/kenba/angle-sc-rs/issues) and [pull requests](https://github.com/kenba/angle-sc-rs/pulls) (open and closed) to ensure that someone else has not noticed it before you. I recommend that you wait for confirmation of your bug or approval for your feature request in this way before starting to code.

Please abide by our [Code of Conduct](CODE_OF_CONDUCT.md) in all issues and pull requests.

## Fork & create a branch

If the issue is something you think that you can fix, then [fork](https://docs.github.com/en/get-started/quickstart/fork-a-repo) this repo and create a branch from the `develop` branch with a descriptive name.  
E.g. a good branch name would be (where issue #42 is the issue you're working on):

```shell
git checkout develop
git checkout -b 42-fix-some-bug
```

## Get the test suite running

Run the unit tests:

```shell
cargo test
```

and integration tests:

```shell
cargo test -- --ignored
```

To ensure that you haven't broken anything.
Please feel free to add tests, especially where the new test(s) demonstrates a bug that you noticed.

Note: a new test that demonstrates a bug that you've described in an issue is always welcome in a PR, even if you haven't developed the code to fix it yet.

## Implement your fix or feature

At this point, you're ready to make your changes!  
Feel free to ask for help; everyone is a beginner at first.

## Get the style right

Your patch should follow the same conventions & pass the same code quality checks as the rest of the project.  
Please instal and run `clippy`, `fmt` and `llvm-cov` before submitting your pull request:

```shell
cargo clippy
cargo fmt
cargo llvm-cov
```

## Make a Pull Request

At this point, you should switch back to your develop branch and make sure it's up to date with opencl3's `develop` branch:

```shell
git remote add upstream git@github.com:kenba/angle-sc-rs.git
git checkout develop
git pull upstream develop
```

Then update your feature branch from your local copy of master, and push it!

```shell
git checkout 42-fix-some-bug
git rebase master
git push --set-upstream origin 42-fix-some-bug
```

Finally, go to GitHub and make a [Pull Request](https://docs.github.com/en/github/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/creating-a-pull-request).

Github Actions will then build your PR.

## Merging a Pull Request

A maintainer will review your PR and determine whether it's Ok to merge it into the `develop` branch.

If it is, he/she will approve and merge the PR. If not, they may comment on the PR to request changes before they are willing to approve and merge it.
Note: at this stage you should only change the PR to resolve the maintainer's comments.

You should *not* introduce a fantastic new feature that you've just thought of! That should be raised as a new issue instead.

## Rebasing a Pull Request

If a maintainer asks you to "rebase" your PR, they're saying that a lot of code has changed, and that you need to update your branch so it's easier to merge.

Github have a good guide about [rebasing in Git](https://docs.github.com/en/get-started/using-git/about-git-rebase) here's our suggested workflow:

```shell
git checkout 42-fix-some-bug
git pull --rebase upstream develop
git push --force-with-lease 42-fix-some-bug
```
