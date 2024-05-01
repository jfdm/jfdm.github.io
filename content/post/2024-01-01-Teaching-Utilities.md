---
title: "Grading Utilities"
tags: ["haskell", "tips", "teaching"]
date: 2024-01-01
---

At work we use Moodle (locally known as MyPlace) for handling course delivery, including the submission and grading of assignments.

Moodle is by far not a perfect system, but it is the one we use.
A primary issue with Moodle is that it is a terribly online system, there are limited ways in which you can work offline and then upload your results.
For instance, MCQs can be written offline and uploaded and so can the returning of marks and feedback.

**As an aside**, and very interestingly, Moodle has the 'rubric' and advanced grading systems that allow one to deconstruct the grading ('divy' up) into non-weighted criteria based on linear scales.
Such advanced grading is not turned on by default.

So grading can be performed offline, and one can download a Spreadsheet or CSV file to do so.
With the downloaded file you can fill in the blanks for each row and then upload the result to Moodle.
A problem with this method, however, is that detailed formatted feedback is harder to produce.
Writing lists in Spreadsheets and CSV files, relegates your feedback to a single line/box.
Multiline feedback in this setting requires some advanced trickery that I am not yet aware off...
Fortunately, Moodle supports uploading of separate, and general, feedback files.
It is not clear however, if you can combine feedback files _and_ rubric grading...

So I decided to write a small utility (locally public at work) to help with offline grading.
It is still in its infancy (beta/alpha if you will), but it is rather promising.

## StrathGrader

The tool (hitherto unnamed, but I am using `StrathGrader` for now) has three modes:

+ **template generation**

  Given:

  + a list of student identifiers
  + a structured document (YAML) presenting weighted criteria

  the tool will generate a YAML file containing a YAML file that will allow one to add scores and feedback for each criterion.

+ **grading**

  Given:

  + a structured document (YAML) detailing a grading scheme
  + a structured document (YAML) presenting weighted criteria
  + a structured document (YAML) presenting the individual grades

  the tool will generate a list of final grades taken from presented grades

+ **pretty**

  Given:

  + a structured document (YAML) presenting the individual grades

  the tool will generate a single formatted Markdown document containing the feedback for each student.

## Example Files

To show the tool in action, and how each file is structured, consider the following.

### Criteria

Let's look at criteria.
The format is:

```
criteria  ::= criterion*
criterion ::= {name :: String, identifier :: String, weight :: Integer}*
```

When dealing with criteria, we _will_ ensure that the weights total to 100, and each criterion is uniquely identified.

One example:

```yaml
criteria:
  - name: Design
    ident: design
    weight: 50
  - name: Functional Correctness
    ident: fc
    weight: 50
```

### Marking Schemes

Now let's look at grading schemes.
`StrathGrader` supports two kinds: qualitative & quantitative.

The format for both is:

```
scheme        ::= classification*
classfication ::= { name :: String, description :: String?, classes }
classes       ::= range* | band*
```

Range depicts quantitative marking, as is defined as:

```
range ::= { name :: String, description :: String?, range :: Interval }
```

where interval is a numeric interval.
When working with a quantitative scheme the ranges must form a non-overlapping interval (start,end) (or is it [start,end])...

Banding represents qualitative marking, and is defined as:

```
band ::= { name :: String, description :: String?
         , range :: Interval, mark*
         }
mark ::= { letter :: String, value :: Integer, description :: String?}
```

here each band represents a grade band in which one can have separate marks.
Like quantitative schemes, bands and marks must form a non-overlapping interval (start,end) (or is it [start,end])...and marks must lie in their band and have a unique letter.

An example of each scheme follows:

+ Quantitative

```yaml
scheme:
  - name: yay
    bands:
      - name: yay
        range:
          to: 2
          from: 2
  - name: maybe
    bands:
      - name: maybe
        range:
          to: 1
          from: 1
  - name: nae
    bands:
      - name: nae
        range:
          to: 0
          from: 0
```

+ Qualitative

```yaml
scheme:
  - name: yay
    bands:
      - name: yay
        range:
          to: 100
          from: 60
        marks:
          - letter: A
            value:  100
          - letter: B
            value:  75
  - name: maybe
    bands:
      - name: maybe
        range:
          to: 59
          from: 30
        marks:
          - letter: C
            value:  50
          - letter: D
            value:  35
  - name: nae
    bands:
      - name: nae
        range:
          to: 34
          from: 5
        marks:
          - letter: E
            value:  30
          - letter: F
            value:  20
  - name: fail
    bands:
      - name: fail
        range:
          to: 4
          from: 0
        marks:
          - letter: G
            value:  0
```

### Results

Finally we have results, which take the form of:

```
results ::= { student :: String, grade :: Integer?
            , feedback :: String?, score* }
score ::=   { identifier :: String, score :: a, feedback :: String? }
```

where `a` is either a letter grade or an integer.
When working with results we need to ensure that the score adheres to both a given criteria and marking scheme.

An interesting bit of research you might say.

An example:


```yaml
results:
  - student: 12345
    grade: null
    feedback: |
      Feedback

      + A feedback
    scores:
      - ident: design
        score: C
        feedback: |
          This was good design.
      - ident: functional
        score: A
        feedback: |
          This was functional
```

## Example Innvocation

So what is the output...well for results generation, we get a single file.

For grading we get a list of student identifiers, their final grade, and the name of their band.
The banding name can help with writing feedback,

```
Grading File
Qualitative
Read Criteria
Read Marking Scheme
Read Scores
Checking Criteria
Tallying
- 12345 75 maybe

```

Finally for pretty printing, we obtain a single markdown file:

```
## 12345
Feedback

+ A feedback
### design (C)
This was good design
### functional
This was functional
```

We can then insert the feedback directly into a single feedback form, or copy and paste into each criteria box.
Alternatively, we can use pandoc to convert this file into HTML for insertion.

Huzzah. It works for now...

## Future work.

Future work will be to make this more moodle friendly.

For instance:

1. generate individual feedback files (Need to find out their formats).
2. generate templates from Moodle CSV files
3. regenerate Moodle CSV files with the final grades when producing the feedback files
4. other stuff...

Anyway time to do some marking...
