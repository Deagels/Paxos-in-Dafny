@echo off

set D=Dafny.exe

for %%X in (%D%) do (set FOUND=%%~$PATH:X)
if defined FOUND (
  if "%1" == "" goto empty
  goto runcompiler
)
echo Can't find %D% in %%PATH%%

:search
for /f %%X in ('dir %D% /b /s') do (
  set dafnydir=%%~dpX
  goto found
)

:nodafny
echo or in current folder. If you have dafny, run this script in the dafny folder to optionally add it to system %%PATH%% and/or compile successfully.
echo You can get Dafny at the following link:
echo.
echo https://dafny.codeplex.com/releases/view/135602
goto end

:found
if not "%1" == "" goto runcompiler
echo Press any key to add %dafnydir% to %%PATH%% system variable.
pause >nul
setx PATH %PATH%;%dafnydir% /m
echo Done
goto end

:empty
echo Usage: Call me with a dfy file as argument or drag-and-drop a file on my icon.
echo To add %D% to %%PATH%%, run without arguments from a folder where %D%
echo can be found.
goto end

:runcompiler
call %D% %1

:end
echo Press any key to exit . . .
pause >nul