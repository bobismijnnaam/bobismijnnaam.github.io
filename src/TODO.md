> FIXME

* I can't find out if a script is from a block editor or the main scripting block. this.parentThatIsA(BlockEditorMorph) does not seem to work in Blocks.js. I need this to distinguish
between translating a single script present in an edit BYOB window to Boogie and translating all the scripts corresponding to BYOBs present in the main scripting window.

* BoogieExpressions are initialised twice.

> IMPROVEMENTS

* Error message for assert fail should come out of corresponding block and not top block.

* Assertion fail messages will look nicer if pop up window shows the block itself.

* Be able to use global variables.

* When editors open for verification, place them around the screen and not one over the other.

* Throw errors 

* Change operators from strings to objects (one for each operator)

* Felienne Hermans wrote on scratch or snap about teaching. Look for paper.

* You can re-declare variables in Snap while Boogie complains of repeated name. We currently compile anyway.

* Inputs are inmutable in Boogie, this is kind of a problem because it is not the case for Snap! and usually we use blocks as methods and not functions. 