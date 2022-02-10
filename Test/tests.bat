@echo off
setlocal enabledelayedexpansion

cd tests

echo start %date% %time% > %~dp0\out.txt

for /R %dir% %%i in (*.sv) do (

  echo | set /p=%%i >> %~dp0\out.txt

  call %~dp0\SVTest.exe -q %%i

  if !ERRORLEVEL! equ 0 (
    findstr "should_fail_because" %%i >NUL 2>&1 && (
      echo | set /p=",MISS" >> %~dp0\out.txt
    )
  ) else (
    findstr "should_fail_because" %%i >NUL 2>&1 || (
      echo | set /p=",ERROR" >> %~dp0\out.txt
    )
  )

  echo, >> %~dp0\out.txt

)

echo end %date% %time% >> %~dp0\out.txt
endlocal

pause
