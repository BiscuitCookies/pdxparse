# pdxparse
A parser for scripts used in Paradox Development Studios games, written in Haskell.

Currently only Europa Universalis IV and Hearts of Iron IV are supported,
but there are plans for other games as well.

This script read the game files and outputs text formatted into wiki tables and templates
Examples of what it currently outputs on the HoI4 wiki
https://hoi4.paradoxwikis.com/Ethiopian_national_focus_tree/scriptoutput for national focuses
https://hoi4.paradoxwikis.com/Swiss_events/scriptoutput for events

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
    -w, --withlabels               the top level of the extra files is considered a label which gets localized, but not processed further
    -f FILE, --file=FILE           also process FILE without any special handling
    -c FILE, --countryscope=FILE   also process FILE as containing code in the counrty scope
    -s FILE, --provincescope=FILE  also process FILE as containing code in the province scope
    -m FILE, --modifiers=FILE      also process FILE as containing modifiers (if the modifiers are not on the top level of the file, --withlabels has to be used as well)


Without command line options, pdxparse just processes everything it finds and puts
the results in the directory `output`. `--onlyextra` can be used to restrict the output,
but the parsing of the extra files is not content-aware.

## Known Issues

* HoI4
    * Decisions don't have a propper format in the output
    * Multiple RHS scopes don't get parsed(e.g. PREV.PREV)
    * Various lines don't have custom messages yet
    * no icons in modifier statements
    * alias tags aren't properly handled
    * add_ai_strategy not handled (do we want to?)

## To do
Feel extremely free to help with any of these or the issues, I honestly doubt I can do any of these except maybe the additonal formatting

* Clean up/optimize code (probably never, cause I'm not good enough, but should still be done)
* Have time for event to be triggered added to the triggered only part in events
* Add more formatting for various lines, best case scenarion minimal editing is needed to place it on the wiki
* Make ~~add_Building_construction~~, random_list work properly
* Make on_action also add the limits/trigger other than just the action
* Rewrite text output for decison for HoI 4
* ~~Find none ugly solution for events that have no options~~
    * find less ugly solution?
* pretty up add_tech_bonus
* Find out how hostility_reason affects add_to_war
* In localization automatically change color of words, add icons, get nested localization etc.
* make set_politics more elaborate maybe?
* ~~ maybe load scripted_effects, scripted_triggers for parsing? ~~ sort of
* maybe load buildings for parsing?
* deal with alias_tags
* maybe load history/units/ for load_OOB
* maybe load technology for has_tech
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
