@echo off
echo Running %1
echo Enter one parameter per line. Press enter twice to finish.
for /L %%i in (1,1,100) do (
	set /p p1=param nr%i%:
	if ("%p1%"=="") break
)
pause