# pdxparse
A parser for scripts used in Paradox Development Studios games, written in Haskell.

Currently only Europa Universalis IV is supported, but there are plans for
other games as well.

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

`pdxparse` should be run from the command line. It will create a directory
`output` in the current directory. Its structure is the same as that of the game
directory, except that the `.txt` files are directories. Each file in these
directories is one "object": one event, one decision, etc.

If you got EU4 from Steam, `pdxparse` should be able to find it automatically
as long as your steamapps folder is in the default location.  If it's somewhere
else, you'll need to edit `settings.yml` to point to it.

Currently there is no command line processing; it just processes everything it
finds and puts the results in the directory `output`. There is, however, a
clause in Main.hs that restricts the parser to only attempt to process certain
files. This is to make the program finish sooner while testing. If you want to
process only certain files, uncomment those lines, edit the list to include
only the files you want, and rebuild.

## Known Issues

* HoI4
    * ~~random_list with variables won't properly show the variable name currently being fed a straight number to make it work. needs manual checking gf files for editing~~
    * random_list handles only numbers for the weight OR only variables for the weight
    * ~~add_building_sconstruction doesn't handle the contents of province = {} well. needs manual editing~~
    * ~~script doesn't like improperly formatted localizations, doesn't handle a space in front of l_<language> at the top of file~~
    * ~~Decisions aren't parsed and checked for event triggers~~
    * Decisions aren't output into text files
    * Tags aren't localized to country names? Sometimes they are?
    * ~~Doesn't like some uses of ROOT and PREV etc. No clue how to fix it~~
    * Don't know if multiple RHS scopes work (e.g. PREV.PREV)
    * triggers for events aren't looked for in national focuses
    * Various lines don't have custom messages yet
    * ~~Localization files need to be directly in the localisation folder and not the localisation->english folder to work~~
    * ~~There are like 5 events where hidden and picture have the first letter capitilized making them fail to parse~~

## To do
Feel extremely free to help with any of these or the issues, I honestly doubt I can do any of these except maybe the additonal formatting

* Clean up code (probably never, cause I'm not good enough, but should still be done)
* Add parser for national focuses
* Have script look for triggers in national focuses
* Add more formatting for various lines, best case scenarion minimal editing is needed to place it on the wiki
* ~~Replace the files in the HoI4 folder with the edited EU4 files and properly remove mentions of EU4 stuff~~
* Get rid of stuff only for EU4 in HoI4 stuff
* ~~Support mods better by having additional settings and making localization reading more elaborate~~
    * ~~Also make it so check for EU4 or HoI4 for proper folder location?~~
* Make ~~add_Building_construction~~, random_list work properly
* ~~Find propper solution for dealing whith opinion_modifier, on_action file formats~~
* Make on_action also add the limits/trigger other than just the action
* Rewrite parser for decison for HoI 4
* Find none ugly solution for events that have no options
*  ~~random_list, ~~ai_chance~~ and possibly more needs to also handle "add" besides "factor" in their "modifier"~~
