@echo off

for %%X in (dafny) do (set FOUND=%%~$PATH:X)
if defined FOUND (
  if "%1" == "" goto empty
  dafny %1
  echo %~n1.dll
  goto end
)
:nodafny
echo Can't find dafny in %%PATH%%
echo You can get Dafny at http://dafny.codeplex.com/
echo Press any key to open page in your browser
pause >nul

:download
start /MIN http://dafny.codeplex.com/
exit

:empty
echo Usage: Call me with a dfy file as argument or drag-and-drop a file on my icon

:end
echo Press any key to exit . . .
pause >nul