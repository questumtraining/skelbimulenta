Option Explicit
Dim fso, shell, folder, target, wmi, processes, process, cmdline, found
Set fso = CreateObject("Scripting.FileSystemObject")
Set shell = CreateObject("WScript.Shell")
folder = fso.GetParentFolderName(WScript.ScriptFullName)
target = LCase(fso.GetAbsolutePathName(folder & "\app.py"))
Set wmi = GetObject("winmgmts:\\.\root\cimv2")
Set processes = wmi.ExecQuery("SELECT * FROM Win32_Process WHERE Name='python.exe' OR Name='pythonw.exe'")
found = False
For Each process In processes
  cmdline = LCase(process.CommandLine & "")
  If InStr(1, cmdline, target, vbTextCompare) > 0 Then
    process.Terminate
    found = True
  End If
Next
If found Then
  MsgBox "Questum Training sustabdytas.", vbInformation, "Questum Training"
Else
  MsgBox "Paleista Questum Training programa nerasta.", vbInformation, "Questum Training"
End If