@echo off
setlocal
cd /d "%~dp0"
py -3 webapp\app.py
if errorlevel 1 python webapp\app.py
pause
