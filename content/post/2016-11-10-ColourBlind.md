---
title: "Colour Blind Aware Semantic Highlighting"
tags: ["latex","accessibility"]
date: 2016-11-10
---

Yesterday, I gave a talk about my work at [SPLS Nov '16](https://msp-strath.github.io/spls-16/) at the
University of Strathclyde.

In my work I have a data type:

```
data Session : (ty  : Ty)
            -> (old : Context)
            -> (new : ty -> Context)
            -> Type
    where
```

and a function that computes an instance of that type with information to popular the value `old`.

```
Session : List Role -> List (Role, Role) -> Type
Session rs ps = Model.Session....
```

Now I could have provided more meaningful names to these different meanings of `Session`.
However, with semantic highlighting who needs too, right?
My work involves the use of Dependent Types as seen in [Idris](https://www.idris-lang.org), and we use semantic highlighting to provide developers with richer information about programming constructs.
Typically the scheme and practise is often referred to as *Conor's Colours*, and the default values specified in this scheme [are used by Idris](http://idris.readthedocs.io/en/latest/reference/semantic-highlighting.html).

However, it turns out one of the attendees is colour blind, and as a result they didn't realise that the use of:

```
Session
```

on one slide was different to the use of

```
Session
```

on another.
That was annonying for both myself and the attendee.
As a result I searched for a [colour blind friendly colour palette]( http://www.somersault1824.com/wp-content/uploads/2015/02/color-blindness-palette.png) and updated my slides and LaTeX style to be more colour blind friendly.

The colours are defined as:

<div class="cus">

       Name            R     G     B
----- ------------- ----- ----- ------
   1   Black           0     0     0
   2   BlueGreen       0    73    73
   3   SeaGreen        0   146   146
   4   Rose          255   109   182
   5   Salmon Pink   255   182   119
   6   Purple         73     0   146
   7   Blue            0   109   219
   8   Lylac         182   109   255
   9   Sky Blue      109   182   255
  10   Light Bluw    182   219   255
  11   Burgundy      146     0     0
  12   Brown         146    73     0
  13   Clay          219   209     0
  14   Lime Green     36   255    36
  15   Pale Yellow   255   255   109
----- ------------- ----- ----- ------

</div>

The resulting style file is [available online](https://github.com/jfdm/sta-latex/blob/master/colour-blind.sty). Together with macroes for use in prose and for semantic code highlighting as seen in Idris.

**Note**: It turns out The colour palette used is one from a set of palettes [described online](http://mkweb.bcgsc.ca/colorblind/).
In future I might update the style file with more of the palettes.


You can check the [slides themselves](https://jfdm.host.cs.st-andrews.ac.uk/presentation/2016-11-09-SPLS.pdf) for an example.
