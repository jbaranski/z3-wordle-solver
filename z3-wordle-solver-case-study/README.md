## Solving Wordle with Z3: A Case Study
Case study article: https://www.jeffbaranski.com/wordle/z3-wordle-solver.html

This repository contains the supporting source code for the case study above (code is cringe, I don't write code like this at my day job, so please don't judge me)

### Running
- `pip install z3-solver`
- `python3 z3-wordle-solver-simulator.py`
- Will solve all 2309 Wordle answers, using a strategy based on the flags set in the source (the strategies are explained in depth in the case study)

#### Strategy flags
- `ALPHABET_RANGE` - Flag to determine should we add an explicit range for each "letter" from 0-25 to keep it within our alphabet range
- `VALID_GUESS_COUNT` - The number of valid guesses z3 gets before we give up (this is just a fail safe)
- `IS_OPTIMIZE` - Whether we should use the z3.Solver() or z3.Optimize()
- Mutually exclusive flags (can only set one at a time, but none are required)
  - `CF_GUESS` - Character frequency weights over the guess list
  - `CF_ANSWER` - Character frequency weights over the answer list
  - `CPF_GUESS` - Character position frequency over the guess list
  - `CPF_ANSWER` - Character position frequency over the answer list
  - `FREQ_GROUP` - Should we group the frequency soft constraints
  - `NORVIG` - Special Peter Norvig strategy
  - The hardcoded guesses in the Norvig strategy
    ```
    NORVIG_GUESSES = {
        0: 'handy',
        1: 'swift',
        2: 'glove',
        3: 'crump'
    }
    ```
- `PREFER_NO_DUPLICATE_CHARS` - Only use duplicate characters in words when we have to
- `PREFER_2_OR_LESS_DUPLICATE_CHARS` - Don't use MORE than two of the same character in words until we have to

