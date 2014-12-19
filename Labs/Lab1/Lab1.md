# Lab 1
Yu Zhou & Phu Dang


Include your writeup for the Lab 1 questions here. Use correct
Markdown markup. For more details, start with the article
https://help.github.com/articles/github-flavored-markdown




1. Scala Basics: Binding and Scope. For each the following uses of names, give the line where
that name is bound. Briefly explain your reasoning (in no more than 1–2 sentences).
(a) Consider the following Scala code.
1 val pi = 3.14
2 def circumference(r: Double): Double = {
3 val pi = 3.14159
4 2.0 * pi * r
5 }
6 def area(r: Double): Double =
7 pi * r * r
The use of pi at line 4 is bound at which line? The use of pi at line 7 is bound at which
line?


Answer : The use of pi at line 4 is bound at line 3
		 The use of pi at line 7 is bound at line 1



(b) Consider the following Scala code.
1 val x = 3
2 def f(x: Int): Int =
3 x match {
4 case 0 => 0
5 case x => {
6 val y = x + 1
7 ({
8 val x = y + 1
9 y
10 } * f(x - 1))

The use of x at line 3 is bound at which line? The use of x at line 6 is bound at which
line? The use of x at line 10 is bound at which line? The use of x at line 13 is bound at
which line?

Answer : The use of x at line 3 is bound by line 2
		 The use of x at line 6 is bound by line 2
		 The use of x at line 10 is bound by line 2
		 The use of x at line 13 is bound by line 1

		 












