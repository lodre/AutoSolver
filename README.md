# AutoSolver

## Описание файлов

В папке AutoSolver находится реализация тактики auto_solver и вспомогательные определения.

Папка Tests содержит тесты по линейной алгебре с приминением данного алгоритма auto_solver.

## Запуск тестов

Запустить тесты можно командой:

```bash
lake build
```

### Первый запуск

При первом запуске будет локально скачана и скомпилированна библиотека mathlib.

Это может занять около часа.

### Ожидаемый вывод

Пока что вывод может выглядеть так:

```cmd
⚠ [1062/1163] Replayed AutoSolver
warning: ./././AutoSolver//AutoSolver.lean:28:8:declaration uses 'sorry'
Build completed successfully.
```

## Применение

Тактику можно применить для доказательства нетривиальных равенств или утверждений для этого в заголовке нужно указать:

```c++
import AutoSolver
```

А на место доказательства написать:

```c++
by auto_solver
```

## Замечание по работе тактики

На данный момент тактика завершает работу успешно тогда и только тогда, когда она может полностью решить задачу. Частичное решение она не генирирует.
