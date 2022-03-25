import copy
import logging
import random
import time
import z3
from wordle_words import VALID_GUESSES, ANSWERS

logging.basicConfig(
    handlers=[
        logging.FileHandler("output.log", mode='w'),
        logging.StreamHandler()
    ]
)
logging.getLogger().setLevel(logging.INFO)

# The size of the word, 5 means 5 character word
ANSWER_LEN = 5
# Flag to determine should we add an explicit range for each "letter" from 0-25 to keep it within our alphabet range
ALPHABET_RANGE = False
# The number of valid guesses z3 gets before we give up (this is just a fail safe)
VALID_GUESS_COUNT = 1000
# Whether we should use the z3.Solver() or z3.Optimize()
IS_OPTIMIZE = True
# Character frequency weights
CF_GUESS = False
CF_ANSWER = False
CPF_GUESS = False
CPF_ANSWER = False
# Should we group the frequency soft constraints
FREQ_GROUP = False
# Special Peter Norvig strategy
NORVIG = False
NORVIG_GUESSES = {
    0: 'handy',
    1: 'swift',
    2: 'glove',
    3: 'crump'
}

# TODO: Character frequency of just vowels?

# Only use duplicate characters in words when we have to
PREFER_NO_DUPLICATE_CHARS = True
# Don't use MORE than two of the same character in words until we have to
PREFER_2_OR_LESS_DUPLICATE_CHARS = True

if CF_GUESS and CF_ANSWER:
    raise Exception("Don't set both character frequency flags to True")
if CPF_ANSWER and CPF_GUESS:
    raise Exception("Don't set both character position frequency flags to True")
if (CF_GUESS or CF_ANSWER) and (CPF_GUESS or CPF_ANSWER):
    raise Exception("Don't set character frequency and character position frequency flags to True at the same time")

# Result file name suffix
RESULT_SUFFIX = 'optimize' if IS_OPTIMIZE and not NORVIG else 'solver'
if NORVIG:
    RESULT_SUFFIX = f"{RESULT_SUFFIX}.norvig"
# If in optimize mode capture the flags we set in the result suffix
if not NORVIG:
    if IS_OPTIMIZE:
        if CF_GUESS:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-cf_guess"
        if CF_ANSWER:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-cf_answer"
        if CPF_GUESS:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-cpf_guess"
        if CPF_ANSWER:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-cpf_answer"
        if FREQ_GROUP:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}_grouped"
        if PREFER_NO_DUPLICATE_CHARS:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-prefer_no_duplicate_chars"
        if PREFER_2_OR_LESS_DUPLICATE_CHARS:
            RESULT_SUFFIX = f"{RESULT_SUFFIX}-prefer_two_or_less_duplicate_chars"


class CF:
    def __init__(self, character, count, frequency):
        self.character = character
        self.count = count
        self.frequency = frequency

    def __str__(self):
        return f"{self.character},{self.count},{self.frequency}%"


class CPF(CF):
    def __init__(self, index, character, count, frequency):
        super().__init__(character, count, frequency)
        self.index = index

    def __str__(self):
        return f"{self.index},{self.character},{self.count},{self.frequency}%"


def get_cfm(list_of_words):
    # Character frequency map
    cfm = {}
    for word in list_of_words:
        for character in word:
            if character in cfm:
                cfm[character] = cfm[character] + 1
            else:
                cfm[character] = 1
    return cfm


def get_cpfm(list_of_words):
    """
        Could have been combined with get_cfm but keep separate in case we want to do different
        things in the future
    """
    # Character position frequency map
    cpfm = {}
    for word in list_of_words:
        for i in range(len(word)):
            character = word[i]
            k = f"{character}#{i}"
            if k in cpfm:
                cpfm[k] = cpfm[k] + 1
            else:
                cpfm[k] = 1
    return cpfm


def get_cf(tc, cfm):
    """tc=total count, cfm=character frequency map"""
    # Frequency list
    fl = []
    # Frequency sum (sums to ~100 but it's close enough for us)
    fs = 0
    for k, v in sorted(cfm.items(), key=lambda item: item[1], reverse=True):
        f = round((v / tc) * 100, 2)
        fs = fs + f
        fl.append(CF(k, v, f))
    for f in fl:
        logging.debug(str(f))
    logging.debug(f"Total frequency sum is {fs}")
    return fl


def get_cpf(tc, cpfm):
    """
        tc=total count,
        cpfm=character position frequency map

        Divide directly by tc since since each position contains tc characters
    """
    # Frequency list
    fl = []
    # Frequency sum (sums to ~100 but it's close enough for us)
    fs = {'0': 0, '1': 0, '2': 0, '3': 0, '4': 0}
    for k, v in sorted(cpfm.items(), key=lambda item: item[1], reverse=True):
        character, i = k.split("#")
        frequency = round((v / tc) * 100, 2)
        fl.append(CPF(i, character, v, frequency))
        fs[i] = fs[i] + frequency
    for f in fl:
        logging.debug(str(f))
    for k, v in fs.items():
        logging.debug(f"Index {k} total frequency sum is {v}")
    return fl


def get_frequencies():
    VALID_GUESSES.extend(ANSWERS)
    # Valid guess character frequency map
    valid_guess_cfm = get_cfm(VALID_GUESSES)
    cf_vg = get_cf(len(VALID_GUESSES) * ANSWER_LEN, valid_guess_cfm)

    # Answer character frequency map
    answer_cfm = get_cfm(ANSWERS)
    cf_a = get_cf(len(ANSWERS) * ANSWER_LEN, answer_cfm)

    # Valid guess character position frequency map
    valid_guess_cpfm = get_cpfm(VALID_GUESSES)
    cpf_vg = get_cpf(len(VALID_GUESSES), valid_guess_cpfm)

    # Answer character position frequency map
    answer_cpfm = get_cpfm(ANSWERS)
    cpf_a = get_cpf(len(ANSWERS), answer_cpfm)

    return cf_vg, cf_a, cpf_vg, cpf_a


class Result:
    """Result object for one answer simulation (which will eventually be dumped into a csv)"""
    def __init__(self, answer, guesses, time_to_solve):
        self.answer = answer
        self.guesses = guesses
        self.time_to_solve = time_to_solve

    def __str__(self):
        """csv friendly string"""
        return f"{self.answer},{'#'.join(self.guesses)},{len(self.guesses)},{self.time_to_solve}"


def get_current_model_word(letters, model, alphabet):
    """
        Print current string representation of the model
        LIKE: but with #'s instead of alphabet
        letter_0 == "w" and letter_1 == "o" and letter_2 == "r" and letter_3 == "l" and letter_4 == "d"
    """
    return ''.join([alphabet[model[letter_key].as_long()] for letter_key in letters])


if __name__ == '__main__':
    # Our alphabet
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    # Represents each letter in the word as an integer
    # EXAMPLE:
    #   This is a logical representation of the word 'ahead'
    #   letter_0=0=a, letter_1=7=h, letter_2=4=e, letter_3=0=a, letter_4=3=d
    letters = [z3.Int(f"letter_{i}") for i in range(ANSWER_LEN)]
    # Add ANSWERS to VALID_GUESSES, they're separated but we need to guess both ANSWERS and VALID_GUESSES
    VALID_GUESSES.extend(ANSWERS)
    logging.info(f"Number answers={len(ANSWERS)}, number valid guesses (including answers)={len(VALID_GUESSES)}")
    # Build a disjunction of all words the solver can guess
    # EXAMPLE:
    #   (letter_0=0=a AND letter_1=7=h AND letter_2=4=e AND letter_3=0=a AND letter_4=3=d) OR
    #   (letter_0=0=a AND letter_1=7=h AND letter_2=4=e AND letter_3=0=a AND letter_4=19=t) OR
    #   ....
    all_words_disjunction = []
    for valid_guess in VALID_GUESSES:
        word_conjunction = z3.And([letters[i] == ord(valid_guess[i]) - 97 for i in range(len(valid_guess))])
        all_words_disjunction.append(word_conjunction)
    # Shuffle the ANSWERS array so we can get some variety if we just want to run through a couple before
    # killing the program
    random.shuffle(ANSWERS)
    # TODO: Uncomment to run quick experiments
    # ANSWERS = ['chart','chart','query','vivid','spine','chart']
    # Keep track of simulation results, so we can write to csv later
    results = []
    for random_answer in ANSWERS:
        start_time = time.time()
        # Create the solver
        solver = z3.Optimize() if IS_OPTIMIZE and not NORVIG else z3.Solver()
        # NOTE: Not really needed because all_words_disjunction will prevent guessing outside of
        #       our alphabet range, keep it just to see how it affects the results
        if ALPHABET_RANGE:
            logging.info("Using alphabet range")
            for letter in letters:
                solver.add(letter >= 0, letter <= 25)
        # Add the all_Words_disjunction to the solver
        solver.add(z3.Or(all_words_disjunction))

        if IS_OPTIMIZE and not NORVIG:
            if PREFER_NO_DUPLICATE_CHARS:
                # Prefer non-duplicate letters
                solver.add_soft(z3.Distinct(tuple([letter for letter in letters])), 100)
            if PREFER_2_OR_LESS_DUPLICATE_CHARS:
                for c in alphabet:
                    two_or_less_cc = [letter == ord(c) - 97 for letter in letters]
                    two_or_less_cc.append(2)
                    solver.add_soft(z3.AtMost(tuple(two_or_less_cc)), 100)
            # Add character frequency hints (only available in the Optimize API)
            if CF_GUESS:
                cf_valid_guesses, _, _, _ = get_frequencies()
                logging.info("Using character frequency hints valid guesses")
                for cf in cf_valid_guesses:
                    for letter in letters:
                        if FREQ_GROUP:
                            # Adding id to soft constraint improves performance but hurts the result accuracy
                            solver.add_soft(letter == ord(cf.character) - 97, cf.frequency, cf.character)
                        else:
                            solver.add_soft(letter == ord(cf.character) - 97, cf.frequency)
                    # TODO: experiment with this too?
                    # solver.add_soft(z3.Or(tuple([letter == ord(cf.character) - 97 for letter in letters])), cf.frequency, cf.character)
            elif CF_ANSWER:
                _, cf_answers, _, _ = get_frequencies()
                logging.info("Using character frequency hints answers")
                for cf in cf_answers:
                    if FREQ_GROUP:
                        solver.add_soft(z3.Or(tuple([letter == ord(cf.character) - 97 for letter in letters])), cf.frequency, cf.character)
                    else:
                        solver.add_soft(z3.Or(tuple([letter == ord(cf.character) - 97 for letter in letters])), cf.frequency)
            elif CPF_GUESS:
                _, _, cpf_valid_guesses, _ = get_frequencies()
                logging.info("Using character position frequency hints valid guesses")
                for cpf in cpf_valid_guesses:
                    if FREQ_GROUP:
                        solver.add_soft(letters[int(cpf.index)] == ord(cpf.character) - 97, cpf.frequency, cpf.character)
                    else:
                        solver.add_soft(letters[int(cpf.index)] == ord(cpf.character) - 97, cpf.frequency)
            elif CPF_ANSWER:
                _, _, _, cpf_answers = get_frequencies()
                logging.info("Using character position frequency hints valid guesses")
                for cpf in cpf_answers:
                    if FREQ_GROUP:
                        solver.add_soft(letters[int(cpf.index)] == ord(cpf.character) - 97, cpf.frequency, cpf.character)
                    else:
                        solver.add_soft(letters[int(cpf.index)] == ord(cpf.character) - 97, cpf.frequency)

        # Create a character frequency dictionary of the answer
        random_answer_character_freq = {}
        # For each character in the answer
        for c in random_answer:
            # If the character exists in the dictionary
            if c in random_answer_character_freq:
                # Increment the character frequency by 1
                random_answer_character_freq[c] = random_answer_character_freq[c] + 1
            else:
                # Add the character to the dictionary with a count of 1
                random_answer_character_freq[c] = 1
        logging.info(f"z3 will attempt to answer {random_answer}")
        # z3's guess
        guess = ''
        # Keep track of guess list
        guessed = []
        # While z3 hasn't guessed correctly, loop until it gets it right or we exceed the valid guess range
        while guess != random_answer and len(guessed) < VALID_GUESS_COUNT:
            # Check whether the constraints in the given solver plus are consistent or not
            # logging.info(solver.assertions())
            # logging.info(solver.objectives())

            # Norvig strategy is to always make the same 4 guesses
            if NORVIG and len(guessed) in NORVIG_GUESSES:
                guess = NORVIG_GUESSES[len(guessed)]
            else:
                check_sat = solver.check()
                # Fetch the current guess (NOTE: this throws an exception if the constraints lead to an unsolvable solution)
                model = solver.model()
                # Get the characters of the word from model (which is represented as an integer)
                guess = get_current_model_word(letters, model, alphabet)
            guessed.append(guess)
            logging.info(f"Guess: {guess}")
            # If the guess is correct, we win!
            if guess == random_answer:
                logging.info(f"WINNER! {len(guessed)}")
                break
            # If the guess is not correct, figure out what constraints we're going to add to the solver (stuff that we
            # learned from the wrong guess)
            # Set of characters from the guess not in the answer at all:
            #   random_answer=ahead,guess=chump --> set={c,u,m,p}
            guess_character_not_in_answer = set()
            # A list of (character index,character) tuples from the guess in the correct position for the answer:
            #   random_answer=ahead,guess=chump --> list=[(2,h)]
            guess_character_in_answer_right_position = []
            # A list of (character index,character) tuples from the guess in the word but not in the correct position
            # for the answer:
            #   random_answer=ahead,guess=dears --> list=[(1,d),(2,e),(3, a)]
            guess_character_in_answer_wrong_position = []
            # A set of (character index,character,at most count) tuples where we have determined that guess should not
            # exceed AT MOST 'x' of some character:
            #   random_answer=diver,guess=diddy --> list=[(3,d,1),(4,d,1)]
            guess_character_in_answer_at_most = set()
            # Create a copy of the answer frequency dictionary since we'll be modifying it for this iteration
            random_answer_character_freq_temp = copy.deepcopy(random_answer_character_freq)
            # First check if we have exact character matches from guess in answer, this takes precedence so we do it
            # alone without checking other logic (like letter in wrong position, etc...)
            for c in range(len(guess)):
                if guess[c] == random_answer[c]:
                    guess_character_in_answer_right_position.append((c, guess[c]))
                    random_answer_character_freq_temp[guess[c]] = random_answer_character_freq_temp[guess[c]] - 1
                    # If the current guess character matches answers character, set the guess character to "1"
                    # so we can skip this character when checking other logic (like letter in wrong position, etc...)
                    guess = guess[:c] + '1' + guess[c + 1:]
            # Now check for misplaced and wrong letters
            for c in range(len(guess)):
                # If '1' we already have an exact match for this character in guess to answer, skip out
                if guess[c] == '1':
                    continue
                # If this character in guess exists in the answer
                if guess[c] in random_answer_character_freq_temp:
                    # If this character in guess hasn't exceeded the AT MOST times we expect to see the character
                    if random_answer_character_freq_temp[guess[c]] > 0:
                        # Character in guess exists in answer but is in the wrong position
                        guess_character_in_answer_wrong_position.append((c, guess[c]))
                        # Subtract 1 from the frequency map, so we'll know next time if we used a single character in
                        # guess too many times
                        random_answer_character_freq_temp[guess[c]] = random_answer_character_freq_temp[guess[c]] - 1
                    else:
                        # We used a character in guess too many times, make sure our next guess(es) know the limit
                        guess_character_in_answer_at_most.add((c, guess[c], random_answer_character_freq[guess[c]]))
                else:
                    # The character in guess doesn't exist in answer
                    guess_character_not_in_answer.add(guess[c])
            # Add constraints to the solver for guess characters in the same position as answer
            for i, c in guess_character_in_answer_right_position:
                solver.add(letters[i] == ord(c) - 97)
            # Add constraints to the solver for guess characters not in the correct position for answer
            for i, c in guess_character_in_answer_wrong_position:
                # Add constraint that it's impossible for the character to exist in this letter position
                solver.add(letters[i] != ord(c) - 97)
                # If this character is in the word but not in this position, then it must be in one of the other 4
                # positions (so if letter_0 != <current character> then letter_1 = <current character> OR
                #            letter_2 = <current_character> OR letter_3 = <current character> OR etc...)
                solver.add(z3.Or([letters[j] == ord(c) - 97 for j in range(len(letters)) if j != i]))
            # Add constraints to the solver for guess characters not in the answer at all
            for c in guess_character_not_in_answer:
                # Iterate each letter representation the answer
                for letter in letters:
                    # Add constraint that it's impossible for the character to exist in this letter position
                    solver.add(letter != ord(c) - 97)
            # Add constraints to the solver for guess characters that should appear no more than "X" times in answer
            # Keep track of the characters we processed so far so we don't duplicate our AT MOST constraint
            # (wouldn't hurt anything if we did but would look weird/stupid)
            letters_processed = set()
            for i, c, f in guess_character_in_answer_at_most:
                # Add constraint that it's impossible for the character to exist in this letter position
                solver.add(letters[i] != ord(c) - 97)
                # If we haven't added our cardinality constraint for this character, do it now
                if c not in letters_processed:
                    # Build a tuple that essentially says:
                    #   For all the letters in letter, character <current character> should appear AT MOST 2 times
                    #   letter_0 == <current character> and letter_1 == <current character> etc..., 2
                    at_most_cc = [letter == ord(c) - 97 for letter in letters]
                    at_most_cc.append(f)
                    # Cardinality constraint https://theory.stanford.edu/~nikolaj/programmingz3.html
                    solver.add(z3.AtMost(tuple(at_most_cc)))
                    letters_processed.add(c)
        # Calculate time to solve
        tts = round(time.time() - start_time, 2)
        results.append(Result(random_answer, guessed, tts))
        logging.info(f"Took {tts} seconds to solve")

    # Write out results to csv file (so we can graph stuff later)
    with open(f"results.{RESULT_SUFFIX}.csv", "w") as f:
        f.write('answer,guessed,num_guessed,time_to_solve\n')
        for result in results:
            f.write(f"{result}\n")
