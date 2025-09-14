# База от Microsoft уже содержит playwright + chromium + зависимости
FROM mcr.microsoft.com/playwright/python:v1.45.0-jammy

# Рабочая директория
WORKDIR /app

# Устанавливаем зависимости из requirements.txt
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Копируем ваш код
COPY . .

# Запуск бота
CMD ["python", "bot.py"]
