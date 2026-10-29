@echo off
setlocal
cd /d "%~dp0"

if exist ".venv\Scripts\python.exe" goto venv_ready

where py >nul 2>&1
if not errorlevel 1 goto use_launcher

where python >nul 2>&1
if errorlevel 1 goto no_python
python -c "import sys; raise SystemExit(0 if sys.version_info >= (3,10) else 1)" >nul 2>&1
if errorlevel 1 goto python_too_old
python -m venv .venv
if errorlevel 1 goto setup_failed
goto venv_ready

:use_launcher
py -3 -c "import sys; raise SystemExit(0 if sys.version_info >= (3,10) else 1)" >nul 2>&1
if errorlevel 1 goto python_too_old
py -3 -m venv .venv
if errorlevel 1 goto setup_failed

:venv_ready
".venv\Scripts\python.exe" -c "import cryptography" >nul 2>&1
if errorlevel 1 (
  echo Installing the required library. Internet access is needed on first launch.
  ".venv\Scripts\python.exe" -m pip install --disable-pip-version-check -r requirements.txt
  if errorlevel 1 goto install_failed
)

set "QUESTUM_HOST=127.0.0.1"
set "QUESTUM_PORT=8000"
echo.
echo Questum Training is starting. Open http://127.0.0.1:8000 in your browser.
echo Leave this window open while using the app. Press Ctrl+C here to stop.
echo.
".venv\Scripts\python.exe" "%~dp0app.py"
if errorlevel 1 goto run_failed
goto done

:no_python
echo Python 3.10 or newer is required. Install Python and run this file again.
goto error_exit

:python_too_old
echo Python 3.10 or newer is required. Install a newer version and run this file again.
goto error_exit

:setup_failed
echo Could not create the local Python environment.
goto error_exit

:install_failed
echo Could not install the required library. Check your internet connection and try again.
goto error_exit

:run_failed
echo The app stopped because of an error.
goto error_exit

:error_exit
pause
:done
endlocal