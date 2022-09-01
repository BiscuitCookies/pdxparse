# pdxparse
A parser for scripts used in Paradox Development Studios games, written in Haskell.

Currently only Europa Universalis IV and Hearts of Iron IV are supported,
but there are plans for other games as well.

## Building

The easiest way to get it running is to use
[GHCup](https://www.haskell.org/ghcup/). Install it, then
`cd` to the directory where you cloned `pdxparse` and type:

    $ stack install --install-ghc

This will automatically install the compiler and all dependencies. (If you
already have GHC 8.10.7 installed, you can probably omit `--install-ghc`.)

You may also be able to just use `cabal-install` if you have it:

    $ cabal install --prefix=/path/to/install

## Usage

Rename settings_example.yml to settings.yml and optionally change game, version
and the steam_ folders if you don't use HOI4 in the default steam location.

`pdxparse` should be run from the command line. It will create a directory
`output` in the current directory. Its structure is the same as that of the game
directory, except that the `.txt` files are directories. Each file in these
directories is one "object": one event, one decision, etc. Normally it will
wait for a user input at the end so that it can be used in a command window
which closes automatically (use `--nowait` to change that).

The following command line options are supported:

    -h, --help      show a help about the command line options
    -p, --paths     show location of configuration files and exit
    -v, --version   show version information and exit
    -n, --nowait    don't wait for the user to press a key before exiting

In addition to that, EU4 parsing supports the following additional options, each of which can be used multiple times:

    -e, --onlyextra                skip writing normal game files and only write the result of parsing
                                       the files which are specified in the following options
    -f FILE, --file=FILE           also process FILE without any special handling
    -c FILE, --countryscope=FILE   also process FILE as containing code in the counrty scope
    -s FILE, --provincescope=FILE  also process FILE as containing code in the province scope
    -m FILE, --modifiers=FILE      also process FILE as containing modifiers


Without command line options, pdxparse just processes everything it finds and puts
the results in the directory `output`. `--onlyextra` can be used to restrict the output,
but the parsing of the extra files is not content-aware.

## Known Issues

* HoI4
    * ~~random_list with variables won't properly show the variable name currently being fed a straight number to make it work. needs manual checking gf files for editing~~
    * ~~random_list handles only numbers for the weight OR only variables for the weight~~
    * ~~add_building_sconstruction doesn't handle the contents of province = {} well. needs manual editing~~
    * ~~script doesn't like improperly formatted localizations, doesn't handle a space in front of l_<language> at the top of file~~
    * ~~Decisions aren't parsed and checked for event triggers~~
    * ~~Decisions aren't output into text files~~
    * Decisions don't have a propper format in the output
    * ~~Tags aren't localized to country names, requires loading history files?~~
    * ~~Doesn't like some uses of ROOT and PREV etc. No clue how to fix it~~
    * Multiple RHS scopes don't get parsed(e.g. PREV.PREV)
    * ~~triggers for events aren't looked for in national focuses~~
    * Various lines don't have custom messages yet
    * ~~Localization files need to be directly in the localisation folder and not the localisation->english folder to work~~
    * ~~There are like 5 events where hidden and picture have the first letter capitilized making them fail to parse~~
    * ~~Fractions can be written as 0.15 or .15 the second case the parser sees it as text instead of a double~~
    * ~~add_country_leader, promote_character aren't processed. Would probably need to load common/characters for it to be properly handled.~~
    * ~~add_ideas, remove_ideas can have multiple ideas in an array, but they aren't handled (no clue how to do it)~~
    * no icons in modifier statements
    * alias tags aren't properly handled
    * ~~equipment_bonus modifier isn't handled~~
    * add_ai_strategy not handled (do we want to?)
    * ~~Need to manually add a closing bracket "}" for SOV.txt in common/ideas to work~~

## To do
Feel extremely free to help with any of these or the issues, I honestly doubt I can do any of these except maybe the additonal formatting

* Clean up/optimize code (probably never, cause I'm not good enough, but should still be done)
* ~~Add text output for national focuses~~
* Have time for event to be triggered added to the triggered only part in events
* ~~Have script look for triggers in national focuses~~
* Add more formatting for various lines, best case scenarion minimal editing is needed to place it on the wiki
* ~~Replace the files in the HoI4 folder with the edited EU4 files and properly remove mentions of EU4 stuff~~
* ~~Support mods better by having additional settings and making localization reading more elaborate~~
    * ~~Also make it so check for EU4 or HoI4 for proper folder location?~~
* Make ~~add_Building_construction~~, random_list work properly
* ~~Find propper solution for dealing whith opinion_modifier, on_action file formats~~
* Make on_action also add the limits/trigger other than just the action
* Rewrite text output for decison for HoI 4
* ~~Find none ugly solution for events that have no options~~
    * find less ugly solution?
*  ~~random_list, ~~ai_chance~~ and possibly more needs to also handle "add" besides "factor" in their "modifier"~~
* pretty up add_tech_bonus
* ~~find none ugly solution for ppOne for [pdx| %lhs = %rhs |], [pdx| %lhs > %rhs |], [pdx| %lhs < %rhs |]~~
* Find out how hostility_reason affects add_to_war
* In localization automatically change color of words, add icons, get nested localization etc.
* make set_politics more elaborate maybe?
* ~~ maybe load scripted_effects, scripted_triggers for parsing? ~~ sort of
* ~~maybe load characters for parsing?~~
    * ~~create hashmap er edit idea hashmap based of idea_token in characters, also useful for has_idea, remove_idea etc.~~
* maybe load buildings for parsing?
* ~~deal with add_ideas, remove_ideas having multiple ideas in them~~
* ~~set_autonomy make it also deal with vars and pronouns for the target (outside foldcompound?)~~
* deal with alias_tags
* maybe load history/units/ for load_OOB
* maybe load technology for has_tech
* m~~aybe load country_leader for traits~~
* handle or ignore add_ai_strategy?
* Expand info on add_field_marshal_role ?
* Expand info of set_building_level
* Find cleaner solution for missing closing brackets in files

## Thanks
* Thanks the functional programming discord community for helping me out and in specific:
    * Edmundnoble
    * skykanin سكايكانن
    * Cyrus T
    * let morrow = fix error
