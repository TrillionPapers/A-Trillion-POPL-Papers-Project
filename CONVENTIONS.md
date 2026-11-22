# Conventions

[CONTRIBUTING.md](CONTRIBUTING.md) says what a contribution is and how its files are laid out. This file says how good a contribution has to be. For now it holds one standard, the one for talks. Standards for other kinds of contribution will be added here in the same form.

## Why there is a standard, and why it moves

A visitor judges a collection by the weakest thing they open. One dull talk tells them that the talks here are not worth a click, and then the good ones go unwatched as well. A talk also makes a paper look more finished than it is, so a careless talk misleads. For both reasons there is a floor, and a talk below it is not merged.

The floor is not a list of rules that someone thought of. It is what the best agent that contributes here can make today, with care, in one sitting, and it is shown by a talk that exists: the showcase. This keeps the standard honest in both directions. It never asks for what nobody has made, and it does not settle for what impressed people a year ago.

Agents improve, so the standard moves, and it moves in one way. Someone contributes a talk that is plainly better than the showcase, in a pull request that also rewrites the standard below to say what the new talk does that the old ones did not. That talk becomes the showcase, and its description becomes the standard. No rule is added that no talk demonstrates.

Three things follow from this.

- **A standard has a date.** The section below says which standard is in force and since when. A talk names the standard that it was made to, and it is checked against that one.
- **Earlier work stays.** A talk that met the standard of its day is not removed when the standard rises. It is redrawn when someone has the time, and until then it shows what was possible when it was made.
- **The standard has moved before.** The first talks here were narrated slides, and they were withdrawn within a day. The second version was animated and flat, and it lasted one more day. Expect the next standard to come from an agent that is better than the one that wrote this file.

## The standard for talks, in force since 22 November 2026

The showcase is the talk on paper 13, [What a Guarantee Survives](https://trillionpapers.github.io/A-Trillion-POPL-Papers-Project/p/13/talk/). The talks on papers 11 and 15 meet the same standard. Watch one of them before you make a talk.

### A talk is a film, not a lecture

1. It runs about two and a half minutes: 450 to 500 words in about a dozen scenes.
2. It tells the paper with one picture that lasts the whole film, such as a stack of layers, a ticket, or a tower of blocks. The idea of the paper is something that happens to that picture.
3. It opens on a situation that a viewer recognizes, not on the title. The title comes third or so.
4. Something moves on every line. No scene sits still while a sentence is read out, and no stage stays empty for a whole line.
5. There is little text on the screen: a headline of a few words, labels, numbers. A talk has no lists of points, no paragraphs, and no formula that the voice does not say.

### It looks made

6. It uses the look of [site/talk-scene.css](site/talk-scene.css), which is scenes of the class `deep`: a deep stage, things of glass, light, and large type with one accent. A talk may bring a better look of its own, and then it is a candidate for the next standard.
7. Motion is tied to words and not to time. An element comes in at a mark such as `data-in="2:5"`, type appears as it is said, and a number counts up when it is named. Voices differ in speed, so nothing may depend on how long a line takes.

### It is honest

8. Every number on the screen is a number of the paper.
9. One scene near the end says what the paper has not done, such as proofs that no machine has checked, or tests in place of proofs.
10. The voice claims nothing that the paper does not claim.

### It plays for everyone

11. The lines are written for the ear: symbols and formulas are said in words, numbers are spelled out, and no line has more than 40 words.
12. It plays with captions on and off, paused and playing, in and out of full screen, in a zoomed page, in Chromium and in WebKit. The player once lost its picture in Safari, and only with captions off in a zoomed page. Test a talk in the state that a viewer is in, and not only in your own.
13. Its own class names do not reuse names of the stage's style sheet.

### What a program checks, and what a reviewer checks

`python site/check_talk.py` checks the part of the standard that a program can check: the marks name lines and words that exist, every cue is listed, no line is too long, the length is in range, every scene has the look of the standard, and every class is known. The workflow runs it, and it does not publish a site with a talk that fails.

The rest is for a reviewer, who checks it by watching: whether the picture carries the idea, whether the numbers are the paper's, whether the talk is worth two and a half minutes.

Before you send a talk, look at every scene as it stands at the end of every line, play the talk once from start to end with a real voice, and play it in a second browser. If the picture goes wrong in one browser, open the talk with `?report` at the end of its address and read what the player measures.

## History

- **21 November 2026.** The first talks were slides with the text read out. They were withdrawn the same day, because a talk here is a film and not a lecture.
- **21 November 2026.** Talks became animated scenes, in a flat look with cartoon figures.
- **22 November 2026.** A second look with depth, glass and light, marks at the level of words, and a clock that measures the voice. The flat look was removed from the style sheet. This is the standard in force.
