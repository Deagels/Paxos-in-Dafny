# Paxos-in-Dafny
Paxos consensus algorithm implemented in the functional validation language Dafny

### Installing for Windows
Get the [latest version of Dafny](https://dafny.codeplex.com/releases/view/135602). The compiler does not require a setup process and you may simply extract the zip somewhere befitting. If you have [Visual Studio](https://www.visualstudio.com/) 2010 or newer installed you may also install the Dafny Language Extension by opening the file *DafnyLanguageService.vsix*

### Compiling
Open paxos.dfy with *Dafny.exe* or *dfy-compile.bat*. If *dfy-compile.bat* can't find *Dafny.exe*, run it once without arguments where it can find it and add it to the %PATH% system variable. After this, *dfy-compile.bat* can be used from anywhere.

**Notes:** Dafny runs in a .NET environment. Make sure you have [.NET Framework 4](http://www.microsoft.com/net) installed