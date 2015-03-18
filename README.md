# Paxos-in-Dafny
Paxos consensus algorithm implemented in the functional validation language Dafny

### Installing for Windows
Get the [latest version of Dafny](https://dafny.codeplex.com/releases/view/135602). The compiler does not require a setup process and you may simply extract the zip somewhere befitting. If you have [Visual Studio](https://www.visualstudio.com/) 2010 or newer installed you may also install the Dafny Language Extension by opening the file *DafnyLanguageService.vsix*

### Compiling
Open paxos.dfy with *Dafny.exe* or *dfy-compile.bat*. If *dfy-compile.bat* can't find *Dafny.exe*, run it once without arguments where it can find it and add it to the %PATH% system variable. After this, *dfy-compile.bat* can be used from anywhere.

**Notes:** Dafny runs in a .NET environment. Make sure you have [.NET Framework 4](http://www.microsoft.com/net) installed

### Installing for Mac OS X (and possibly Linux)
Download and install [Mono](https://dafny.codeplex.com).
Get the [latest version of Dafny](https://dafny.codeplex.com). Install (unzip) Dafny to a suitable folder (e.g. inside the `Paxos-in-Dafny` folder).
Get the [Z3 theorem prover](http://z3.codeplex.com). Unzip the Z3 folder inside the Dafny folder. Make a symbolic link to the `z3.exe` file from the Dafny folder (where the `Dafny.exe` file resides). This is so that Dafny can find Z3.

### Running Dafny from the terminal (with Mono)
Open a terminal window and run:
```sh
cd Paxos-in-Dafny
mono Dafny/Dafny.exe paxos.dfy
```
